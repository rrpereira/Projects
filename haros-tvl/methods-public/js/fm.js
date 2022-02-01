fetch("http://localhost:5000/", {
  method: "POST", // or 'PUT'
  headers: {
    "Content-Type": "application/json"
  },
  body: JSON.stringify({ feature: "give me the treedata" })
})
  .then((response) => response.json())
  .then((data) => {
    var margin = {
        top: 20,
        right: 120,
        bottom: 20,
        left: 120
      },
      width = 960 - margin.right - margin.left,
      height = 800 - margin.top - margin.bottom;

    var root = data;

    var i = 0,
      duration = 750,
      rectW = 60,
      rectH = 30;

    var tree = d3v3.layout.tree().nodeSize([70, 40]);
    var diagonal = d3v3.svg.diagonal().projection(function (d) {
      return [d.x + rectW / 2, d.y + rectH / 2];
    });

    var svg = d3v3
      .select("#body")
      .append("svg")
      .attr("width", 500)
      .attr("height", 500)
      .call((zm = d3v3.behavior.zoom().scaleExtent([1, 3]).on("zoom", redraw)))
      .append("g")
      .attr("transform", "translate(" + 350 + "," + 20 + ")");

    //necessary so that zoom knows where to zoom and unzoom from
    zm.translate([350, 20]);

    root.x0 = 0;
    root.y0 = height / 2;

    function collapse(d) {
      if (d.children) {
        d._children = d.children;
        d._children.forEach(collapse);
        d.children = null;
      }
    }

    collapse(root);
    update(root);

    d3v3.select("#body").style("height", "800px");

    console.log(root);

    function update(source) {
      // Compute the new tree layout.
      var nodes = tree.nodes(root).reverse(),
        links = tree.links(nodes);

      // Normalize for fixed-depth.
      nodes.forEach(function (d) {
        //To decrease/increase link's depth, the value multiplied by "d.depth" must be changed (original value was 180).
        d.y = d.depth * 90;
      });

      // Update the nodes…
      var node = svg.selectAll("g.node").data(nodes, function (d) {
        return d.id || (d.id = ++i);
      });

      // Enter any new nodes at the parent's previous position.
      var nodeEnter = node
        .enter()
        .append("g")
        .attr("class", "node")
        .attr("transform", function (d) {
          return "translate(" + source.x0 + "," + source.y0 + ")";
        });

      nodeEnter
        .append("rect")
        .attr("width", rectW)
        .attr("height", rectH)
        .attr("stroke", "#8A6D3B")
        .attr("stroke-width", "2px")
        .style("fill", function (d) {
          if (d.selected === true) return "#addea7";
          else if (d.selected === false) return "#fca082";
          else if (d.selected === null) return "#fff";
        })
        .on("click", click);

      nodeEnter
        .append("text")
        .attr("class", "moreFeatures")
        .attr("x", rectW / 2)
        .attr("y", rectH + rectH / 4)
        //.attr("dy", ".35em")
        .attr("text-anchor", "middle")
        .style("letter-spacing", "0.5")
        .style("font-size", "10px")
        .style("fill", "grey")
        .text(function (d) {
          return !d._children || !d._children.length ? null : "...";
        })
        .on("click", click);

      nodeEnter
        .append("text")
        .attr("class", "name")
        .attr("x", rectW / 2)
        .attr("y", rectH / 2)
        //.attr("dy", ".35em")
        .attr("text-anchor", "middle")
        .style("letter-spacing", "0.5")
        .style("font-size", "10px")
        .text(function (d) {
          return d.name;
        })
        .on("click", click);

      nodeEnter
        .append("text")
        .attr("class", "card")
        .attr("x", rectW / 2)
        .attr("y", rectH - rectH / 11)
        .attr("dy", "-.10em")
        .attr("text-anchor", "middle")
        .style("letter-spacing", "0.5")
        .style("font-size", "10px")
        .text(function (d) {
          return "\n\n[" + d.minCard + ".." + d.maxCard + "]";
        })
        .on("click", click);

      nodeEnter
        .append("circle")
        .attr("class", "optCircle")
        .attr("stroke", "black")
        .attr("stroke-width", 1)
        .attr("r", rectW / 15)
        .attr("cx", rectW / 2)
        .attr("cy", 0)
        .style("fill", function (d) {
          return d.opt ? "#fff" : "black";
        });

      nodeEnter
        .append("text")
        .attr("class", "addButtonText")
        .attr("x", 15 * (rectW / 16))
        .attr("y", 0)
        .attr("text-anchor", "middle")
        .style("fill", "green")
        .style("font-size", "14px")
        .attr("dy", "-.05em")
        .attr("font-weight", 700)
        .text("+")
        .on("click", function (d) {
          return changeFM(d, "include");
        });

      nodeEnter
        .append("text")
        .attr("class", "deleteButtonText")
        //.attr("x", rectW - 4 * (rectW / 8 / 2))
        //.attr("y", -rectH / 4 / 16)
        .attr("x", 12 * (rectW / 16))
        .attr("y", 0)
        .attr("text-anchor", "middle")
        .style("fill", "red")
        .style("font-size", "12px")
        .attr("dy", "-.05em")
        .attr("font-weight", 700)
        .text("-")
        .on("click", function (d) {
          return changeFM(d, "exclude");
        });

      // Transition nodes to their new position.
      var nodeUpdate = node
        .transition()
        .duration(duration)
        .attr("transform", function (d) {
          return "translate(" + d.x + "," + d.y + ")";
        });

      nodeUpdate
        .select("rect")
        .attr("width", rectW)
        .attr("height", rectH)
        .attr("stroke", "#8A6D3B")
        .attr("stroke-width", "2px")
        .style("fill", function (d) {
          if (d.selected === true) return "#addea7";
          else if (d.selected === false) return "#fca082";
          else if (d.selected === null) return "#fff";
        });

      nodeUpdate
        .select("text.moreFeatures")
        .attr("x", rectW / 2)
        .attr("y", rectH + rectH / 4)
        //.attr("dy", ".35em")
        .attr("text-anchor", "middle")
        .style("letter-spacing", "0.5")
        .style("font-size", "10px")
        .style("fill", "grey")
        .text(function (d) {
          return !d._children || !d._children.length ? null : "...";
        });

      nodeUpdate.select("text").style("fill-opacity", 1);

      // Transition exiting nodes to the parent's new position.
      var nodeExit = node
        .exit()
        .transition()
        .duration(duration)
        .attr("transform", function (d) {
          return "translate(" + source.x + "," + source.y + ")";
        })
        .remove();

      nodeExit
        .select("rect")
        .attr("width", rectW)
        .attr("height", rectH)
        //.attr("width", bbox.getBBox().width)""
        //.attr("height", bbox.getBBox().height)
        .attr("stroke", "#8A6D3B")
        .attr("stroke-width", "2px")
        .text(function (d) {
          return null;
        });

      //.attr("width", bbox.getBBox().width)""
      //.attr("height", bbox.getBBox().height)
      nodeExit.select("text");

      // Update the links…
      var link = svg.selectAll("path.link").data(links, function (d) {
        return d.target.id;
      });

      // Enter any new links at the parent's previous position.
      link
        .enter()
        .insert("path", "g")
        .attr("class", "link")
        .attr("x", rectW / 2)
        .attr("y", rectH / 2)
        .attr("d", function (d) {
          var o = {
            x: source.x0,
            y: source.y0
          };
          return diagonal({
            source: o,
            target: o
          });
        });

      // Transition links to their new position.
      link.transition().duration(duration).attr("d", diagonal);

      // Transition exiting nodes to the parent's new position.
      link
        .exit()
        .transition()
        .duration(duration)
        .attr("d", function (d) {
          var o = {
            x: source.x,
            y: source.y
          };
          return diagonal({
            source: o,
            target: o
          });
        })
        .remove();

      // Stash the old positions for transition.
      nodes.forEach(function (d) {
        d.x0 = d.x;
        d.y0 = d.y;
      });
    }

    // Toggle children on click.
    function click(d) {
      if (d.children) {
        d._children = d.children;
        d.children = null;
      } else {
        d.children = d._children;
        d._children = null;
      }
      update(d);
    }

    // Select/Unselect a feature and its dependents.
    function changeFM(d, string) {
      fetch("http://localhost:5000/" + string, {
        method: "POST", // or 'PUT'
        headers: {
          "Content-Type": "application/json"
        },
        body: JSON.stringify({ feature: d.name })
      })
        .then((response) => response.json())
        .then((data) => {
          console.log("Success!! :", data.features);
          changeSelections(d, data.features);
          //TODO: The resetConfig fetch needs to be inserted inside window.App.configurations.fetch(); technically that is already being done but the window.App.configurations.fetch() must be applied in some other way because it is causing an error.
          window.App.configurations
            .fetch()
            .then((data) => {
              console.log("Success:", d);
              update(d);
              fetch("http://localhost:5000/resetConfig", {
                method: "POST", // or 'PUT'
                headers: {
                  "Content-Type": "application/json"
                },
                body: JSON.stringify({ feature: d.name })
              })
                .then((response) => response.json())
                .then((data) => {})
                .catch((error) => {
                  console.error("Error:", error);
                });
            })
            .catch((error) => {
              console.error("Error:", error);
            });
        })
        .catch((error) => {
          console.error("Error:", error);
        });
    }

    //Unassign a feature and its dependents.
    /*function unassign(d) {
      fetch("http://localhost:5000/unassign", {
        method: "POST", // or 'PUT'
        headers: {
          "Content-Type": "application/json"
        },
        body: JSON.stringify({ feature: d.name })
      })
        .then((response) => response.json())
        .then((data) => {
          console.log("Success:", data);
          changeSelections(d, data.features);
          update(d);
        })
        .catch((error) => {
          console.error("Error:", error);
        });
    }*/

    //Redraw for zoom
    function redraw() {
      //console.log("here", d3v3.event.translate, d3v3.event.scale);
      svg.attr(
        "transform",
        "translate(" +
          d3v3.event.translate +
          ")" +
          " scale(" +
          d3v3.event.scale +
          ")"
      );
    }

    function changeSelections(d, changed) {
      changeSelectionsRec(goToRoot(d), changed);
    }

    function changeSelectionsRec(d, changed) {
      if (changed != {}) {
        if (changed.hasOwnProperty(d.name)) {
          d.selected = changed[d.name];
          delete changed[d.name];
        }
        if (d.hasOwnProperty("_children") && d._children)
          for (child of d._children) changeSelectionsRec(child, changed);
        if (d.hasOwnProperty("children") && d.children)
          for (child of d.children) changeSelectionsRec(child, changed);
      }
    }

    function goToRoot(d) {
      if (d.parent) return goToRoot(d.parent);
      else return d;
    }
  })
  .catch((error) => {
    console.error("Error:", error);
  });
