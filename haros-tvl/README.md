# HAROS-TVL

Robotic systems are a key part of the current technological boom, but despite all their advantages, there are some obstacles preventing their widespread use, in particular related to safety when operating in critical contexts. In fact, several tragic accidents have already occurred with autonomous vehicles. The key question is then how to make safe and reliable robotic systems? It is not an easy task, as building a robot requires many different interdisciplinary techniques and tools.

## Tools
<img src="https://upload.wikimedia.org/wikipedia/commons/thumb/9/99/Unofficial_JavaScript_logo_2.svg/260px-Unofficial_JavaScript_logo_2.svg.png" width="100" height="100">&nbsp;&nbsp;&nbsp;&nbsp;<img src="https://www.ros.org/imgs/logo-white.png" width="378" height="100">&nbsp;&nbsp;&nbsp;&nbsp;[![alt text](https://camo.githubusercontent.com/586ccf0aad9684edc821658cee04146cf36d1f1d5ec904bbefd72728909ccb2e/68747470733a2f2f64336a732e6f72672f6c6f676f2e737667)](https://d3js.org/)&nbsp;&nbsp;&nbsp;&nbsp;[<img src="https://avatars.githubusercontent.com/u/9950313?s=200&v=4" width="100" height="100">](https://nodejs.org/)

[![alt text](https://raw.githubusercontent.com/git-afsantos/haros/master/logo.png)](https://github.com/git-afsantos/haros)


## Abstract

[ROS](https://www.ros.org/) is a framework that provides a set of tools and libraries to build robotic systems and [HAROS](https://github.com/git-afsantos/haros) promotes the quality of these systems. HAROS-TVL is an extension to HAROS and its goal is to bring Software Product Lines field knowledge and apply it to the software that is developed with ROS. By using HAROS-TVL, robot developers can immediately have a better insight and understanding of the application they have in hands, whether it is theirs or a third-party one.

After analysing the domain of the application to build, there are some independent software pieces or sets of features that are considered as features. These features are grouped into a model that formaly depictes the existing interactions and constraints between all of them. Having and understanding this model, is crucial for the developer to know what he can do with a certain ROS application.

Besides giving developers a formal tool to build robotic systems, HAROS-TVL also allows them to interact with it, making the selection/deselection of features a very straightforward process.


## Code explanation

HAROS-TVL is an extension to HAROS, therefore it only introduces new changes in some parts of the latter. The web page that is launched is visualy different in the Models tab - it has a feature diagram and the computation graph changes according to the state of the feature diagram. The issues under Issues tab are also updated according to the state of the feature diagram. This means that the source code related with HAROS-TVL consists in changing this web page and building from scratch the new server that replaces the one that was previously used to launch HAROS viz.

This server has two primary functions: provide the information to launch the web page and handle the operations that are requested by the user in the feature diagram. As the user interactes with the feature diagram, multiple operations occur: selecting/deselecting features, colapsing/expanding feature's children, computation graph adjustments, etc. Of those, the more complex operations are selecting and deselecting features which force the state of the feature model to change. 

The workflow is the following:
* the file paths are checked;
* the feature model is validated;
* the TVL file is compared to the launch file;
* the JSON file that will later be converted to the feature diagram is created;
* the server waits for requests on the routes "/include", "/exclude", "/resetConfig" and "/", respectively:
  + to include a feature;
  + to exclude a feature;
  + to reset the content the data files;
  + to reset the data in the feature model.

  
<!--## Execution

This section shows how to run the specification in the ToolBox and other aspects metioned above.-->


## Setup

This stage assumes that all of the required instalations regarding the use of HAROS were already done. Both [instalation](https://github.com/git-afsantos/haros/blob/master/INSTALL.md) and [usage](https://github.com/git-afsantos/haros/blob/master/docs/USAGE.md) procedures are available in the [HAROS](https://github.com/git-afsantos/haros) page. It also assumes that Node.js is already installed.

The proper execution of HAROS-TVL requires the existence of a launch file built acording to the TVL feature model. This whole process is explained in [this]() document. (HAROS-TVL runs the following files with default paths: launch file, TVL feature model, JSON containing the exported data and JSON containing the issues - this is a temporary measure.)    

After completing all the previous steps, open a terminal, and move to a directory where you want to clone this repository.

```bash
mkdir ros
cd ros
git clone https://github.com/rrpereira/haros-tvl
cd haros-tvl
```

Install the packages needed for the project to properly run.

```bash
npm install
```

Run HAROS with a project file of your own. There is no need to launch HAROS web server, because HAROS-TVL has its own and it uses the exported data. For example: 

```bash
haros analyse -n -p <path to the project file>
```

By starting the HAROS-TVL server, it is possible to open a web page in localhost at the specified port.

```bash
npm start
```

HAROS-TVL is now ready to be used.

## Execution

This section shows how HAROS-TVL extension looks like.

### Running HAROS-TVL 

In this demonstration, the HAROS-TVL web page is launched, the user navigates to the Models tab, and includes/excludes some features. This operations are passed on to the server that changes the state of the feature model internally and consequently removes or resolves the elements in the computation graph.

https://user-images.githubusercontent.com/36520545/151946227-f51aa488-4083-4cf1-8f8c-b3004eaa1902.mp4


