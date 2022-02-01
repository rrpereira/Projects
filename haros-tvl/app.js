/**
 * This server is a complement to HAROS (https://github.com/git-afsantos/haros) and its final goal is to add an extra functionality to better handle variability. First of all, it introduces in HAROS the concept of feature model, allowing the user to properly group the existing features (ROS resources). Then, it allows the user to interact with that feature model by selecting and deselecting features as he sees fit. As the user interactes with the feature model, multiple operations occur: selecting/deselecting features, colapsing/expanding feature's children, computation graph adjustments, etc. In essence, it eases the comprehension process of a ROS application.
 *
 * The workflow is the following:
 *    - the file paths are checked;
 *    - the feature model is validated;
 *    - the TVL file is compared to the launch file;
 *    - the JSON file that will later be converted to the feature diagram is created;
 *    - the server waits for requests on the routes "/include", "/exclude", "/resetConfig" and "/", respectively:
 *      + to include a feature
 *      + to exclude a feature
 *      + to reset the content the data files;
 *      + to reset the data in the feature model.
 *
 * Some of the technologies/libraries used in this server are:
 *    - TVL (https://projects.info.unamur.be/tvl/) - A language complemented with a Java library that makes the feature model interactible.
 *    - NPM java package (https://www.npmjs.com/package/java) - an NPM package that acts as a "bridge API to connect with existing Java APIs"
 *    - D3 (https://bl.ocks.org/d3noob/8375092#index.html) - a JavaScript library that makes data viewable.
 */

const express = require("express");
const morgan = require("morgan");
const java = require("java");
const { json } = require("express");
const fs = require("fs");
const fse = require("fs-extra");
const parser = require("xml2json");
const builder = require("xmlbuilder");
const path = require("path");
const { features } = require("process");
const os = require("os");
const { generateKeyPairSync } = require("crypto");

const app = express();

//Loading data folder created by HAROS.
fse.copySync(
  os.homedir() + "/.haros/viz/data",
  "./methods-public/data",
  { overwrite: true } /*,
  //This callback will cause the ./methods-public folder to be loaded before the data folder is copied from ./haros/viz, which will result in a bad behaviour. Yet, this callback ensures the copy was/wasn't made. Therefore, the ./methods-public must be loaded only after this copy.
  function (err) {
    if (err) {
      console.error(err);
    } else {
      console.log("Data loaded from HAROSviz folder.");
      
    }
  }*/
);
//Loading all the front-end sources.
app.use(express.static("./methods-public"));

app.use(express.urlencoded({ extended: false }));
app.use(express.json());
app.use(morgan("tiny"));

//Generic launch file.
//lf = os.homedir() + "/catkin_ws/src/turtlerand/launch/launch_files4/general_includes4_copy.launch"
//lf = "resources/launch/turtlebot/generic_turtlebot.launch";
lf = os.homedir() + "/catkin_ws/src/turtlerand/launch/generic.launch";
//lf = os.homedir() + "/catkin_ws/src/lizi/lizi/launch/generic.launch";

//TVL file.
ftmfilepath = "resources/feature_models/turtlerand/turtlerand.tvl";
//ftmfilepath = "resources/feature_models/turtlebot/turtlebot.tvl";
//ftmfilepath = "resources/feature_models/lizi/lizi.tvl";

//TODO: This is hardcoded; imagine that the project changes from SAFER to something else...
//HAROSviz file with information about how to draw the HAROSviz' computation graph.
vizData = "methods-public/data/SAFER/configurations.json";
//HAROSviz file with information about HAROSviz' generic issues.
//TODO: This is hardcoded; imagine that the runtime issues file changes its name //"generic" to something else...
issuesData = "methods-public/data/SAFER/compliance/runtime/generic.json";
//TODOTODO "issuesToDeleteData" must be deleted (as well as other actions with "TODOTODO" MARK) as soon as HAROS is able to assign a conditions array with condition objects to each "generic.json"
issuesToDeleteData =
  "methods-public/data/SAFER/compliance/runtime/genericToDelete.json";

//Loading the TVLParser library.
java.classpath.push("./TVLParser-20100804/TVLParser-20100804/TVLParser.jar");

//Loading the TVLParser modules.
TVLParser = java.import("be.ac.info.fundp.TVLParser.TVLParser");
FeatureModel = java.import("be.ac.info.fundp.TVLParser.Util.FeatureModel");
FeatureSymbol = java.import(
  "be.ac.info.fundp.TVLParser.symbolTables.FeatureSymbol"
);
IDGenerator = java.import("be.ac.info.fundp.TVLParser.Util.IDGenerator");
File = java.import("java.io.File");

//TODO: The server must check the existence of these files before using them, and that is not being done yet. These accesses must be done syncronously with the rest of the code.To do so, everything that must be done after that should be inside readFile callback. Another option is to use promisses.
//Checking the existence of the following files.
const checkFilesAccess = async () => {
  try {
    /*await*/ fs /*.promisses*/.access(vizData, fs.R_OK, (err) => {
      if (err) console.log(`File ${vizData} doesn't exist`);
      else console.log(`File ${vizData} exists`);
    });
    //TODOTODO "issuesToDeleteData" must be corrected to "issuesData" as soon as HAROS is able to assign a conditions array with condition objects to each "generic.json"
    /*await*/ fs /*.promisses*/.access(issuesToDeleteData, fs.R_OK, (err) => {
      if (err) console.log(`File ${issuesToDeleteData} doesn't exist`);
      else console.log(`File ${issuesToDeleteData} exists`);
    });
    /*await*/ fs /*.promisses*/.access(lf, fs.R_OK, (err) => {
      if (err) console.log(`File ${lf} doesn't exist`);
      else console.log(`File ${lf} exists`);
    });
    /*await*/ fs /*.promisses*/.access(ftmfilepath, fs.R_OK, (err) => {
      if (err) console.log(`File ${ftmfilepath} doesn't exist`);
      else console.log(`File ${ftmfilepath} exists`);
    });
  } catch (error) {
    console.log(error);
  }
};

checkFilesAccess();

//Instantiating/declaring the TVL parser.
var tvlParser = new TVLParser(new File(ftmfilepath));

//Checking TVL file feature model validity.
if (!tvlParser.isValidSync())
  if (!tvlParser.isSyntacticallyCorrectSync()) {
    console.log(
      `TVL file ${path.parse(ftmfilepath).base} has syntactic errors.`
    );
    return;
  } else if (!tvlParser.isCorrectlyTypedSync()) {
    console.log(`TVL file ${path.parse(ftmfilepath).base} has type errors.`);
    return;
  }

/*
try {
  //Getting all possible products.
  products = tvlParser
    .getSolutionsSync()
    .map((solution) =>
      solution.filter(
        (symbol) =>
          (s = IDGenerator.getInstanceSync().getSymbolSync(symbol)) &&
          s != null &&
          !s.getIDSync().includes("ArtificialParent")
      )
    )
    .filter(((t = {}), (a) => !(t[a] = a in t)));

  //Print number of features and number of possible configurations.
  console.log(
    `${tvlParser
      .getRootSync()
      .getIDSync()} app has ${tvlParser.nbFeaturesSync()} features and ${
      products.length
    } possible configurations.`
  );
} catch (e) {
  logMyErrors(e);
}*/

//Instantiating/declaring a TVL feature model.
var fm = new FeatureModel(tvlParser.getRootSync());

/** configurationsOri and configurations both have the content of the "configurations" file (which the path is given by "vizData"); since, no changes should be done directly in the file (let's imagine the app crashes or something else occurs, then the file must not have changes resulting from the interaction of the user with the TVL structure, in order to be used again later), it was decided that:
 * the configurations variable will be modified everytime the user includes/excludes a feature on TVL structure;
 * then, its (configurations's) content will be printed on the configurations file;
 * then, the web client will call a function to redraw the computation graph (based on the new "configurations" file);
 * and finally the web client will request the server to put back on the "configurations" its original content which is always stored in configurationsOri.
 * This way, "configurations" file will always have the content produced by HAROS except during that time the user exlcudes/includes a feature - if for some reason the app crashes between the moment the server writes "configurations" and the moment the server writes "configurationsOri" in the file, than the HAROS must redo the "configurations" file.
 */
//Loading the content of vizData JSON file to configurationsOri and to configurations.
let configurationsOri = JSON.parse(fs.readFileSync(vizData, "utf-8"));
let configurations = JSON.parse(fs.readFileSync(vizData, "utf-8"));

//Loading the content of issuesData JSON file to genericOri and to generic (the idea is the same as for vizData).
//TODO: The "generic" variable's name doesn't make sense since the generic.json file can change its name
//TODOTODO "issuesToDeleteData" must be corrected to "issuesData" as soon as HAROS is able to assign a conditions array with condition objects to each "generic.json"
let genericOri = JSON.parse(fs.readFileSync(issuesToDeleteData, "utf-8"));
//TODOTODO "issuesToDeleteData" must be corrected to "issuesData" as soon as HAROS is able to assign a conditions array with condition objects to each "generic.json"
let generic = JSON.parse(fs.readFileSync(issuesToDeleteData, "utf-8"));

//TODO: The server must check if the TVL structure matches launch file args before using both, and that is not being done yet. This check must be done syncronously with the rest of the code. To do so, everything that must be done after that should be inside readFile callback. Another option is to use promisses.
//Checking if TVL structure features match launch file args (nodes).
/*const start = async () => {
  try {
    if (
      !TVLmatchesLF(
        fm
          .getModelSync()
          .toArraySync()
          .filter(
            (el) => (n = el.getNameSync()) && !n.includes("ArtificialParent")
          )
          .map((ft) => ft.getNameSync()),
        lf
      )
    )
      throw new Error();
  } catch (error) {
    console.log(error);
  }
};
start();*/
fs /*.promisses*/.readFile((LFfilepath = lf), function (err, data) {
  if (err) {
    console.log("error:", err);
    return false;
  }
  TVLfeatures = fm
    .getModelSync()
    .toArraySync()
    .filter((el) => (n = el.getNameSync()) && !n.includes("ArtificialParent"))
    .map((ft) => ft.getNameSync());
  var lfContent = JSON.parse(parser.toJson(data));
  if (!lfContent.launch.arg.every((arg) => TVLfeatures.includes(arg.name))) {
    unmatchingArgs = lfContent.launch.arg
      .filter((arg) => !TVLfeatures.includes(arg.name))
      .map((arg) => arg.name);
    throw new Error(
      `TVL structure features does not match the following launch file args: ${JSON.stringify(
        unmatchingArgs
      )}`
    );
  }
});

//TODO: This verification is the same as the previous but it is done in concern to "configurations" file nodes.
//Checking if TVL structure features match with "configurations" file features.
/*if (
  !TVLmatchesConfigurations(
    fm
      .getModelSync()
      .toArraySync()
      .filter((el) => (n = el.getNameSync()) && !n.includes("ArtificialParent"))
      .map((ft) => ft.getNameSync()),
    configurations[0]["nodes"].map((node) => path.parse(node.name).base);
  )
)
  return 0;*/

//To see the content of configurations.
//console.log("configurations:\n", JSON.stringify(configurations));

//To see the content of generic.
//console.log("generic:\n", JSON.stringify(generic));

//Converting the provided TVL structure into a JSON which will be used later by d3 on the client side.
treeData = jsonize(tvlParser.getRootSync(), null);

//Logging TVL structure converted in JSON.
//console.log("TVL in JSON:\n", JSON.stringify(treeData));

//Accessing/refreshing the HAROSviz page, which initializes/resets data).
app.post("/", (req, res) => {
  //Initializing the feature model on which the server will rely to handle everything related to the TVL structure. If this handler is triggered after a previous execution, then "fm" will (at first) contain an instance of FeatureModel with some elements already included/excluded.
  fm = new FeatureModel(tvlParser.getRootSync());

  //Initializing "configurations", which will contain modified data from "configurations.json" file if the user refreshes the HAROSviz page.
  configurations = JSON.parse(fs.readFileSync(vizData, "utf-8"));

  //TODOTODO "issuesToDeleteData" must be corrected to "issuesData" as soon as HAROS is able to assign a conditions array with condition objects to each "generic.json"
  //Initializing "generic", which will contain modified data from "generic.json" file if the user refreshes the HAROSviz page.
  generic = JSON.parse(fs.readFileSync(issuesToDeleteData, "utf-8"));

  return res.status(200).json(treeData);
});

//TODOTODO "issuesToDeleteData" must be corrected to "issuesData" as soon as HAROS is able to assign a conditions array with condition objects to each "generic.json"
//Reseting the content of "configurations" and "generic" file to its original state.
app.post("/resetConfig", (req, res) => {
  fs.writeFile(vizData, JSON.stringify(configurationsOri), function () {
    fs.writeFile(issuesToDeleteData, JSON.stringify(genericOri), function () {
      return res.status(200).json({ msg: "Configurations and issues reseted" });
    });
  });
});

//"/include": Changing the state of the desired feature in the TVL structure to "included", if that is possible. This may change the state to "included"/"excluded" of other TVL structure features which are dependent of this one. This method also changes the content of the "configuration" file according to the actual TVL structure state which is reflected later in the HAROSviz computation graph.
//"/exclude": Changing the state of the desired feature in the TVL structure to "excluded", if that is possible. This may change the state to "included"/"excluded" of other TVL structure features which are dependent of this one. This method also changes the content of the "configuration" file according to the actual TVL structure state which is reflected later in the HAROSviz computation graph. These "configuration" file changes are burdensome comparing to the ones done in the "/include" post request handler, since removing a node means it has to dissapear from the computation graph, as well as all the data which is depending on it.
app.post(["/include", "/exclude"], (req, res) => {
  /**
   * TODO: Get the fdelement and directly question if it is selected or not not depending on the automatic selections. This will be possible if TVL library gets fixed.
   * TODO: model = fm.getModelSync().toArraySync().filter(el => 0===el.getNameSync().localeCompare(req.body.feature))[0]
   */

  //Declaring the response object which will contain the state of each feature.
  var object = {};

  //TODO: fm.isSelectableSync(req.body.feature, false) || fm.isUnSelectableSync(req.body.feature, false) && !fm.isExcludedSync(req.body.feature, false) -> this was the previous if conditions which could be simplified to fm.isUnassignedSync(req.body.feature, false)
  //Checking if the feature is selectable or unselectable, meaning includable or excludable (it may be already "included"/"excluded" sometimes).
  if (fm.isUnassignedSync(req.body.feature, false)) {
    if (
      req.url.includes("/include") &&
      fm.isSelectableSync(req.body.feature, false)
    )
      //Changing the state of the TVL structure by including the desired feature and including/excluding its dependents.
      fm.includeSync(req.body.feature, false);
    else if (
      req.url.includes("/exclude") &&
      fm.isUnSelectableSync(req.body.feature, false) &&
      !fm.isExcludedSync(req.body.feature, false)
    )
      //Changing the state of the TVL structure by excluding the desired feature and including/excluding its dependents.
      fm.excludeSync(req.body.feature, false);

    //Creating the response object which will contain the state of each feature.
    object["msg"] = `${req.body.feature} and its dependents were ${req.url}d`;
    object["features"] = {};

    //Exporting the TVL structure features to an array which contains every feature diagram element (including "artificial parents").
    fm.getModelSync()
      .toArraySync()
      .map(
        (el) =>
          //Getting the name of the feature.
          (n = el.getNameSync()) &&
          //Ignoring the feature if it is an "artificial parent" (if so, this expression returns false and the following one won't even be done).
          !n.includes("ArtificialParent") &&
          //Filling the response object with each feature and its state (which is calculated with functions such as "isIncludedSync" and "isUnassignedSync"). "true" indicates that the feature is included, "false" indicates that it is excluded and "null" that it is neither.
          (object["features"][n] = fm.isIncludedSync(n, false)
            ? true
            : fm.isUnassignedSync(n, false)
            ? null
            : false)
      );

    //Logging the response object.
    //console.log(object);

    //Logging the feature diagram elements with their state.
    /*console.log(
      fm
        .getModelSync()
        .toArraySync()
        .map((el) => el.toStringSync())
    );*/

    //Logging configurations var.
    //console.log("configurations: \n", JSON.stringify(configurations));

    //Logging generic var.
    //console.log("generic: \n", JSON.stringify(generic));

    //TODO: NOT EVERYHTING THAT IS WHITHIN THE CONDITIONS ARRAY IS AN "argument which corresponds to a feature". There are other args which are not features, therefore, some elements are apearing because the conditions or another array is not empty, when what should be verified was whether that array contains "object" features or not.
    //Removing from each node in "configurations" file, every element of the array conditions where its corresponding feature in TVL is already included or excluded (depending on the "statement" field, "if" or "unless", respectively). In this file, each node has an array conditions. Each element of this array is an operand of a conjunction (it can be true or false), therefore, in order to its node become solid (not dashed) in the computation graph, the array must be empty (which means that it has no conditions). The same operation must be done in topics, parameters and services. Another situation is when the node is when the node (or other elements) disapears, something that is handled below on the code.
    for (element of ["nodes", "topics", "parameters", "services"])
      configurations[0][element].forEach((node) => {
        node.conditions = node.conditions.filter((cond) => {
          //Getting the state of the feature referenced inside the actual condition of array conditions.
          featureState =
            object["features"][
              cond.condition.substring(
                cond.condition.lastIndexOf(" ") + 1,
                cond.condition.indexOf(")")
              )
            ];
          /*Filtering the elements of the array conditions which 
                the "statement" has the value "if" and their corresponding feature in TVL is true (included) or 
                the "statement" has the value "unless" and their corresponding feature in TVL is false (excluded). 
            More specifically, those array elements which meet one of the two previous constraints are removed from the array.*/
          return !(
            (featureState == true && cond["statement"] === "if") ||
            (featureState == false && cond["statement"] === "unless")
          );
        });
      });

    //Stores the names of the nodes excluded from the "configurations" file.
    excluded = [];
    //Stores the names of the topics excluded from the "configurations" file.
    excludedTopics = [];

    //This filter will check in "nodes" property, which is an array, if its element contains in its conditions included or excluded features, with "unless" or "if" statements, respectively. If so, the name of this element/node is stored in "excluded" array and the information regarding to that element is removed from the file. One may question: why is this array needed if it is possible to retrive the excluded features from the feature diagram? That is because not every feature in the feature diagram corresponds to a computation graph node, yet, every node will be conditioned by at least a feature. Let's think about the Turtlerand example: there is a node named Multiplexer but it isn't represented by a feature in the feature model; yet, Multiplexer will only appear as solid (included) in the computation graph if features named Random and Teleop become included. That way, since Multiplexer's conditions in "configurations" contains Random and Teleop, if one of this becomes excluded, the Multiplexer will be excluded too from nodes property in "configurations" file - as well as all the information related to Multiplexer. If the server was only relying on the excluded features in the feature diagram, the "configurations" file data related with Multiplexer would not be removed, causing, for instance, links, to and from Multiplexer to still appear even thought Multiplexer node image was not there.
    configurations[0]["nodes"] = configurations[0]["nodes"].filter((node) => {
      //Checking if some condition from conditions is false. If so, a true boolean value will be returned.
      nodeLeaves = node["conditions"].some((condition) => {
        //Getting the state of the feature referenced inside the actual condition of array conditions.
        featureState =
          object["features"][
            JSON.stringify(condition).substring(
              JSON.stringify(condition).lastIndexOf(" ") + 1,
              JSON.stringify(condition).indexOf(")")
            )
          ];
        /*Filtering the elements of the array nodes which have in their conditions array at least one element where 
                the "statement" has the value "if" and their corresponding feature in TVL is false (excluded) or 
                the "statement" has the value "unless" and their corresponding feature in TVL is true (included). 
          More specifically, those nodes array elements which meet one of the two previous constraints are removed from the array, as well as any information related with them in the file.*/
        return (
          (featureState === false && condition["statement"] === "if") ||
          (featureState === true && condition["statement"] === "unless")
        );
      });

      //Adding the actual node to "excluded" in case of existing some false condition.
      if (nodeLeaves) excluded.push(path.parse(node["name"]).base);

      //Nodes whether no false condition was found will be retrieved.
      return !nodeLeaves;
    });

    //Removing from "configurations" file property "topics" information related with excluded features. In property "topics", properties "publishers" and "subscribers" are arrays containing the names of the nodes which publish to or subscribe that topic. If the node was removed than its name must be removed from both arrays (if it is there).
    configurations[0]["topics"] = configurations[0]["topics"].filter(
      (topic) => {
        for (link of ["publishers", "subscribers"])
          topic[link] = topic[link].filter(
            (linkElem) => !excluded.includes(path.parse(linkElem).base)
          );

        //TODO: conditions were not being verified under topics and other properties.... now, in topics conditions, at the presence of one feature that is also in excluded array, the topic is eliminated; what is happening is that cmd_vel_high topic is being wrongly given the Random feature as a condition. in fact all topics are conditioned by random; this must be some HAROS bug. i will comment this and the return to avoid the error ...                 that error appears with the removal of a topic that is related to a feature other than Random, the Turtlesim feature; by removing this topic, there is a link in links that won't have access to that topic when it should have because that topic shouldnt be removed
        topicLeaves = topic["conditions"].some((condition) =>
          excluded.includes(
            JSON.stringify(condition).substring(
              JSON.stringify(condition).lastIndexOf(" ") + 1,
              JSON.stringify(condition).indexOf(")")
            )
          )
        );

        if (topicLeaves) excludedTopics.push(topic["name"]);

        //Topics whether both "publishers" and "subscribers" arrays are empty won't be retrived (since a topic without any connection to nodes is useless).
        return (
          Boolean(topic["publishers"].length || topic["subscribers"].length) &&
          !topicLeaves
        );
      }
    );
    console.log(JSON.stringify(configurations));
    console.log(excluded);

    //Removing from "configurations" file properties "publishers", "subscribers", "writes", "reads", "clients" and "servers", information related with excluded features. For each property, its property "node" contains the name of the node which was or was not removed and property "topic" contains the name of the topic it is linked to.
    for (link of [
      "publishers",
      "subscribers",
      "reads",
      "writes",
      "servers",
      "clients"
    ])
      configurations[0]["links"][link] = configurations[0]["links"][
        link
      ].filter(
        (linkElem) =>
          !excluded.includes(path.parse(linkElem["node"]).base) &&
          !excludedTopics.includes(linkElem["topic"])
      );

    //Removing from "configurations" file property "parameters" information related with excluded features. In property "parameters", property "reads" is an array containing the names of the nodes which read data from that parameter. Only the names of those nodes which were not removed will stay in the "reads" array of each parameter.
    configurations[0]["parameters"] = configurations[0]["parameters"].filter(
      (parameter) => {
        for (parameterType of ["reads", "writes"])
          parameter[parameterType] = parameter[parameterType].filter(
            (elem) => !excluded.includes(path.parse(elem).base)
          );

        //Parameters where "reads" and "writes" property arrays are empty won't be retrieved.
        return Boolean(parameter["reads"].length || parameter["writes"].length);
      }
    );

    configurations[0]["services"] = configurations[0]["services"].filter(
      (service) => {
        for (serviceType of ["clients", "servers"])
          service[serviceType] = service[serviceType].filter(
            (elem) => !excluded.includes(path.parse(elem).base)
          );

        //Services where "clients" and "servers" property arrays are empty won't be retrieved.
        return Boolean(service["clients"].length || service["servers"].length);
      }
    );

    configurations[0]["queries"] = configurations[0]["queries"].filter(
      (query) => {
        query["objects"] = query["objects"].filter(
          (obj) => !excluded.includes(path.parse(obj["name"]).base)
        );

        //Queries where "objects" property array is empty won't be retrieved.
        return query["objects"].length;
      }
    );

    //TODOTODO "genericToDelete.json" file name must be changed to "generic.json" as soon as HAROS starts to include conditions array in every issue object.
    //Removing for each issue in "genericToDelete.json" file array, every element of the array conditions (assuming that HAROS is already including a conditions array in every element of "genericToDelete.json" array, and the "statement" atribute as well) where its corresponding feature in TVL is already included/excluded. In this file, each issue has (or is supposed to have) an array conditions. Each element of this array is an operand of a conjunction (it can be true or false), therefore, if a feature is included/excluded (and "statement" is "if"/"unless", respectively) in the computation graph, the issue remains in the list (the following code block), otherwise (feature gets excluded/included and and "statement" is "if"/"unless", respectively) the issue is deleted (the code block after the following).
    for (element of generic)
      element["conditions"] = element["conditions"].filter((cond) => {
        featureState =
          object["features"][
            cond.condition.substring(
              cond.condition.lastIndexOf(" ") + 1,
              cond.condition.indexOf(")")
            )
          ];

        return !(
          (featureState === true && cond["statement"] === "if") ||
          (featureState === false && cond["statement"] === "unless")
        );
      });

    //TODOTODO "genericToDelete.json" file name must be changed to "generic.json" as soon as HAROS starts to include conditions array in every issue object.
    //This filter will check in "genericToDelete.json" file, which is an array, if its elements contain in its conditions included/excluded features (and "statement" is "unless"/"if", respectively). If so, the corresponding issue object is removed from "genericToDelete.json" file.
    generic = generic.filter((issue) => {
      //Checking if some condition from conditions is false. If so, a true boolean value will be returned.
      return !issue["conditions"].some((condition) => {
        featureState =
          object["features"][
            JSON.stringify(condition).substring(
              JSON.stringify(condition).lastIndexOf(" ") + 1,
              JSON.stringify(condition).indexOf(")")
            )
          ];

        return (
          (featureState === false && condition["statement"] === "if") ||
          (featureState === true && condition["statement"] === "unless")
        );
      });
    });

    //TODO: The same way properties "links", "topics", "parameters", "services" and "nodes" were scanned to apply new changes, other properties from "configurations" json file may need to be scanned such as: "dependendices", "launch", "environment" and "hpl" and may be others. These were the ones available at the time of writing this comment.
  } else
    object = {
      msg: "This feature is not selectable/unselectable.",
      features: []
    };

  //Writing in the "configurations.json" file the new state of the HAROSviz computation graph which will later be redesigned by HAROSviz according to the most recent changes.
  fs.writeFile(vizData, JSON.stringify(configurations), (err) => {
    if (err) console.log(err);

    //TODOTODO the following writeFile function signature must be deleted (the writeFile function inside and the return statment within it remains untouched) as soon as HAROS is able to assign a conditions array with condition objects to each "generic.json"
    //Writing in the "generic.json" file the filtered issues according to the most recent changes.
    fs.writeFile(issuesToDeleteData, JSON.stringify(generic), (err) => {
      if (err) console.log(err);

      fs.writeFile(issuesData, JSON.stringify(generic), (err) => {
        if (err) console.log(err);

        //Returning the "object" response.
        return res.status(200).json(object);
      });
    });
  });
});

/*Giving the user the possibility of unassign a feature, but that is not working yet in TVL library.
app.post("/unassign", (req, res) => {
  // Get the fdelement and directly question if it is selected or not not depending on the automatic selections
    //model = fm.getModelSync().toArraySync() 
    //fdElement = model.filter(el => 0===el.getNameSync().localeCompare(req.body.feature))[0]
  try {
    //if(isUnassignedSync(req.body.feature, false) && isUnselected(req.body.feature, false)){
    fm.unassingSync(req.body.feature, false);
    var object = {};
    object["msg"] = `${req.body.feature} and its dependents were unassigned`;
    object["features"] = {};
    fm.getModelSync()
      .toArraySync()
      .map(
        (el) =>
          (n = el.getNameSync()) &&
          !n.includes("ArtificialParent") &&
          (object["features"][el.getNameSync()] = fm.isIncludedSync(n, false)
            ? true
            : fm.isUnassignedSync(n, false)
            ? null
            : false)
      );
    console.log(object);
    return res.status(200).json(object);
  } catch {
    return res.status(200).json({
      msg: "This feature is not unssignable",
      features: []
    });
  }
});*/

/*Giving the user the possibility of generating all the possible launch files according to the exclusions of inclusions made in the feature model.
IDGenerator = java.import("be.ac.info.fundp.TVLParser.Util.IDGenerator");
IDGenerator.getInstanceSync()
              .getSymbolSync(intProdutos[i][j])
              .getIDSync()
Symbol = java.import("be.ac.info.fundp.TVLParser.symbolTables.Symbol");
app.get("/generate", (req, res) => {
  console.log(
    fm
      .getModelSync()
      .toArraySync()
      .map((el) => el.toStringSync())
  );
  fs.readFile(lf, function (err, data) {
    var lfContent = JSON.parse(parser.toJson(data));
    //console.log(lfContent)
    lfArgs = lfContent.launch.arg.map((arg) => arg.name);
    fmFeatures = fm
      .getModelSync()
      .toArraySync()
      .filter((el) => (n = el.getNameSync()) && !n.includes("ArtificialParent"))
      .map((ft) => ft.getNameSync());
    console.log(fmFeatures);
    console.log(lfArgs);
    //se os argumentos do launch file forem os mesmos que as features do feature model
    if (fmFeatures.sort().join(",") === lfArgs.sort().join(",")) {
      //se alguma vez a biblioteca permitir recalcular o parser com os includes e os excludes do utilizador então deve-se substituir este parser aqui em baixo pelo recalculado..
      //extração dos produtos para um array de arrays
      intProdutos = tvlParser.getSolutionsSync();

      console.log(intProdutos);
      intProdutos = intProdutos
        .map((p) =>
          p.filter(
            (pe) =>
              (s = IDGenerator.getInstanceSync().getSymbolSync(pe)) &&
              s != null &&
              !s.getIDSync().includes("ArtificialParent")
          )
        )
        .filter(((t = {}), (a) => !(t[a] = a in t)));
      stringProdutos = [];

      intProdutos.map(function (p, i) {
        var jsonXML = { launch: {} };
        allProducts = fmFeatures;
        stringProdutos.push([]);
        jsonXML["launch"]["arg"] = [];
        jsonXML["launch"]["include"] = { "@name": lf, arg: [] };
        p.map(function (pe, j) {
          stringProdutos[i].push(
            IDGenerator.getInstanceSync()
              .getSymbolSync(intProdutos[i][j])
              .getIDSync()
          );
          jsonXML["launch"]["arg"].push({
            "@name": stringProdutos[i][j],
            "@value": "true"
          });
          jsonXML["launch"]["include"]["arg"].push({
            "@file": stringProdutos[i][j],
            "@value": "$(arg " + stringProdutos[i][j] + ")"
          });
        });

        fmFeatures
          .filter((el) => !stringProdutos[i].includes(el))
          .map(function (pe, k) {
            jsonXML["launch"]["arg"].push({ "@name": pe, "@value": "false" });
            jsonXML["launch"]["include"]["arg"].push({
              "@name": pe,
              "@value": "$(arg " + pe + ")"
            });
          });

        var xml = builder.create(jsonXML).end({ pretty: true });
        console.log(xml);
        console.log(path.dirname(lf));
        console.log(path.dirname(lf) + "/config" + i + ".launch");
        fs.writeFile(
          path.dirname(lf) + "/config" + i + ".launch",
          xml,
          function (err) {
            if (err) {
              return console.log(err);
            }
            console.log("The file was saved!");
          }
        );
      });


    } else
      console.log(
        "The generic launch file args do not match the feature model!"
      );
  });
  var object = {};
  object["msg"] = `Done with generate.`;
  object["features"] = {};
  return res.status(200).json(object);
});*/

app.listen(5000, () => {
  console.log("Server is listening on port 5000...");
});

/**
 * Recursive function which gets all the info about the current feature and iterates over their children. In the returned object JSON, each feature is represented as an object which contains the following properties:
 *  > name - a string identifying it;
 *  > parent - a string identifying its parent (optional features always have an "artificial parent" created by TVLParser, which is ignored in the current conversion; );
 *  > selected - a boolean to check if the feature is selected or not;
 *  > minCard - an int with the minimum cardinality of the children features;
 *  > maxCard - an int with the maximum cardinality of the children features;
 *  > opt - a boolean to check if the feature is optional;
 *  > children - an array containing objects which are the current feature's children.
 * @author   Ricardo
 * @param    {FeatureSymbol} featureSymbol     Instance of a feature symbol
 * @param    {String} parentArg                String containing the name of the feature's parent
 * @return   {object JSON}                     JSON containing the TVL structure
 */
function jsonize(featureSymbol, parentArg) {
  //Defining the properties of the object.
  var object = {};
  object["name"] = featureSymbol.getIDSync();
  //TODO: When it comes to otpional features, this string already contains the real name of the current feature's parent with the prefix "ArtificialParent". So it is reasonable to question: why does it have the prefix "ArtificialParent"? This prefix is needed to assess later if the object["opt"] is true or false, according to the feature's optionality (the presence of "ArtificialParent" prefix suggests that the feature is optional, meaning object["opt"] is true).
  object["parent"] = parentArg
    ? parentArg.includes("ArtificialParent")
      ? parentArg.replace("ArtificialParent", "")
      : parentArg
    : parentArg;
  object["selected"] = null;
  object["minCard"] = featureSymbol.getMinCardinalitySync();
  object["maxCard"] = featureSymbol.getMaxCardinalitySync();
  object["opt"] = parentArg
    ? parentArg.includes("ArtificialParent")
      ? true
      : false
    : false;
  object["children"] = [];

  //TODO: The TVL parser does not have the isOptionnalSync function working properly, otherwise this (the following commented line) would be the best approach and would also simplify a lot other "object" properties related with artificial parents.
  //object["opt"] = featureSymbol.isOptionnalSync()
  var children = featureSymbol.getChildrenFeaturesSync();

  //If there are no more children, then the current object is returned.
  if (!children) return object;
  var childrenArray = children.valuesSync().toArraySync();

  //For each child of the feature's children, the server calls "jsonize" function, which creates an object and pushes it to the children array of the current feature.
  for (child of childrenArray)
    object["children"].push(
      jsonize(
        child,
        //TODO: (same problem of object["opt"] property). As one can see, the "ArtificialParent" prefix is deliberately being added to the string.
        object.name.includes("ArtificialParent")
          ? "ArtificialParent" + object.parent
          : object["name"]
      )
    );

  //If the current feature is an "artificial parent", then the returned object is its child (which is also the only element of the array, since "artificial parents" only have a child, the optional feature). This is how jsonize function is ignoring and discarding "artificial parent" features from the final object JSON.
  return object.name.includes("ArtificialParent") ? object.children[0] : object;
}

/*In case one finds out how to call this function syncronously before tree data calculation.*/
// function TVLmatchesLF(TVLfeatures, LFfilepath) {
//   fs /*.promisses*/.readFile(LFfilepath, function (err, data) {
//     if (err) {
//       console.log("error:", err);
//       return false;
//     }

//     var lfContent = JSON.parse(parser.toJson(data));

//     return lfContent.launch.arg.every((arg) => TVLfeatures.includes(arg.name));
//   });
// }*/

/*In case one finds out how to call this function syncronously before tree data calculation.*/
// function TVLmatchesConfigurations(TVLFeatures, ConfigFeatures) {
//   fs /*.promisses*/.readFile(ConfigFeatures, function (err, data) {
//     if (err) {
//       console.log("error:", err);
//       return false;
//     }

//     var ConfigFeaturesContent = JSON.parse(parser.toJson(data));

//     return ConfigFeaturesContent.launch.arg.every((arg) => TVLfeatures.includes(arg.name));
//   });
// }*/
