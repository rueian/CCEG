@extends('main')

@section('jumbotron')
<div class="jumbotron">
  <div class="container">
    <h1 class="display-3">
      <a href="#" data-pk="{{ $blueprint->id }}" data-name="name" data-type="text" data-url="{{ url('/blueprints/editable') }}" data-title="流程名稱" data-editable="">{{ $blueprint->name }}</a>
    </h1>
    <p class="lead">
      <a href="#" data-pk="{{ $blueprint->id }}" data-name="note" data-type="textarea" data-url="{{ url('/blueprints/editable') }}" data-title="說明備註" data-emptytext="說明備註" data-editable="">{{ $blueprint->note }}</a>  
    </p>
  </div>
</div>
@endsection

@section('container')

<div class="row">
  <div class="col-md-2 col-sm-4 col-xs-6">
    <a href="#" data-toggle="modal" data-target="#storageModal" class="btn btn-lg btn-light btn-block border-secondary mb-3" style="min-height: 10rem; display: table;">
      <div class="card text-center bg-transparent border-0" style="display: table-cell; vertical-align: middle;">
        <div class="card-body text-center">
          <p class="card-text text-secondary" style="font-size: 2rem;">
            <i class="fas fa-plus-circle"></i>
            新增資料
          </p>
        </div>
      </div>
    </a>
  </div>

  <div class="col-md-2 col-sm-4 col-xs-6">
    <a href="#" data-toggle="modal" data-target="#stepModal" class="btn btn-lg btn-light btn-block border-secondary mb-3" style="min-height: 10rem; display: table;">
      <div class="card text-center bg-transparent border-0" style="display: table-cell; vertical-align: middle;">
        <div class="card-body text-center">
          <p class="card-text text-secondary" style="font-size: 2rem;">
            <i class="fas fa-plus-circle"></i>
            新增運算
          </p>
        </div>
      </div>
    </a>
  </div>
</div>

<div class="row">
    <div class="col-md-12">
        <div id="layout-controls" class="controls joint-theme-default">
            <label for="ranker">Ranker:</label>
            <select id="ranker">
                <option value="network-simplex" selected="">network-simplex</option>
                <option value="tight-tree">tight-tree</option>
                <option value="longest-path">longer-path</option>
            </select>
            <label for="rankdir">RankDir:</label>
            <select id="rankdir">
                <option value="TB" selected="">TB</option>
                <option value="BT">BT</option>
                <option value="RL">RL</option>
                <option value="LR">LR</option>
            </select>
            <label for="align">Align:</label>
            <select id="align">
                <option value="UL" selected="">UL</option>
                <option value="UR">UR</option>
                <option value="DL">DL</option>
                <option value="DR">DR</option>
            </select>
            <label for="ranksep">RankSep:</label>
            <input id="ranksep" type="range" min="1" max="100" value="50">
            <label for="edgesep">EdgeSep:</label>
            <input id="edgesep" type="range" min="1" max="100" value="50">
            <label for="nodesep">NodeSep:</label>
            <input id="nodesep" type="range" min="1" max="100" value="50">
        </div>
    </div>
</div>

<div class="row">
  <div class="col-md-12">
    <div id="paper"></div>
  </div>
</div>

<!-- Storage Modal -->
<div class="modal fade" id="storageModal" tabindex="-1" role="dialog" aria-labelledby="storageModalLabel" aria-hidden="true">
  <div class="modal-dialog modal-lg" role="document">
    <div class="modal-content">
      <div class="modal-header">
        <button type="button" class="close" data-dismiss="modal" aria-label="Close"><span aria-hidden="true">&times;</span></button>
        <h4 class="modal-title" id="storageModalLabel">新增資料源</h4>
      </div>
      <div class="modal-body">
          <div id="storageForm"></div>
      </div>
    </div>
  </div>
</div>

<!-- Step Modal -->
<div class="modal fade" id="stepModal" tabindex="-1" role="dialog" aria-labelledby="stepModalLabel" aria-hidden="true">
  <div class="modal-dialog" role="document">
    <div class="modal-content">
      <div class="modal-header">
        <button type="button" class="close" data-dismiss="modal" aria-label="Close"><span aria-hidden="true">&times;</span></button>
        <h4 class="modal-title" id="storageModalLabel">新增步驟</h4>
      </div>
      <div class="modal-body">
        <div id="stepForm"></div>
      </div>
      <div class="modal-footer">
        <button type="button" class="btn btn-secondary" data-dismiss="modal">Close</button>
        <button type="button" class="btn btn-primary">Save changes</button>
      </div>
    </div>
  </div>
</div>

<style>
    #paper {
        border: 1px solid lightgray;
        position: absolute;
        margin-left: auto;
        margin-right: auto;
        left: 0;
        right: 0;
        top: 100px;
    }
    .controls {
        margin: auto;
        text-align: center;
        padding: 10px 0;
        border-bottom: 1px solid lightgray;
        display: inherit;
    }
    .controls input[type="range"] {
        display: inline-block;
        width: auto;
    }
</style>

<template id="link-controls-template">
    <div id="link-controls" class="controls">
        <label for="labelpos">LabelPos:</label>
        <select id="labelpos">
            <option value="c">c</option>
            <option value="r">r</option>
            <option value="l">l</option>
        </select>
        <label for="minlen">MinLen:</label>
        <input id="minlen" type="range" min="1" max="5" value="1">
        <label for="weight">Weight:</label>
        <input id="weight" type="range" min="1" max="10" value="1">
        <label for="labeloffset">LabelOffset:</label>
        <input id="labeloffset" type="range" min="1" max="10" value="10">
    </div>
</template>
@endsection

@section('beforeScript')
<script>
    window.Props = {
        blueprint: @json($blueprint),
        storageFormSchema: @json(App\RuntimeStorage::getAllFormSchema()),
        stepFormSchema: @json(App\Step::getAllFormSchema($blueprint->payload)),
    };
</script>
@endsection

@section('afterScript')
<script>
    var Shape = joint.dia.Element.define('demo.Shape', {
        size: {
            width: 100,
            height: 50
        },
        attrs: {
            rect: {
                refWidth: '100%',
                refHeight: '100%',
                fill: 'ivory',
                stroke: 'gray',
                strokeWidth: 2,
                rx: 10,
                ry: 10
            },
            text: {
                refX: '50%',
                refY: '50%',
                yAlignment: 'middle',
                xAlignment: 'middle',
                fontSize: 30
            }
        }
    }, {
        markup: '<rect/><text/>',

        setText: function(text) {
            return this.attr('text/text', text || '');
        }
    });

    var Link = joint.dia.Link.define('demo.Link', {
        attrs: {
            '.connection': {
                stroke: 'gray',
                strokeWidth: 2,
                pointerEvents: 'none',
                targetMarker: {
                    type: 'path',
                    fill: 'gray',
                    stroke: 'none',
                    d: 'M 10 -10 0 0 10 10 z'
                }
            }
        },
        connector: {
            name: 'rounded'
        },
        z: -1,
        weight: 1,
        minLen: 1,
        labelPosition: 'c',
        labelOffset: 10,
        labelSize: {
            width: 50,
            height: 30
        },

    }, {
        markup: '<path class="connection"/>',

        connect: function(sourceId, targetId) {
            return this.set({
                source: { id: sourceId },
                target: { id: targetId }
            });
        },

        setLabelText: function(text) {
            return this.prop('labels/0/attrs/text/text', text || '');
        }
    });

    var LayoutControls = joint.mvc.View.extend({

        events: {
            change: 'layout',
            input: 'layout'
        },

        options: {
            padding: 100
        },

        init: function() {

            var options = this.options;
            if (options.adjacencyList) {
                options.cells = this.buildGraphFromAdjacencyList(options.adjacencyList);
            }

            this.listenTo(options.paper.model, 'change', function(cell, opt) {
                if (opt.layout) {
                    this.layout();
                }
            });
        },

        layout: function() {

            var paper = this.options.paper;
            var graph = paper.model;
            var cells = this.options.cells;

            joint.layout.DirectedGraph.layout(cells, this.getLayoutOptions());

            if (graph.getCells().length === 0) {
                // The graph could be empty at the beginning to avoid cells rendering
                // and their subsequent update when elements are translated
                graph.resetCells(cells);
            }

            paper.fitToContent({
                padding: this.options.padding,
                allowNewOrigin: 'any'
            });

            this.trigger('layout');
        },

        getLayoutOptions: function() {
            return {
                setVertices: true,
                setLabels: true,
                ranker: this.$('#ranker').val(),
                rankDir: this.$('#rankdir').val(),
                align: this.$('#align').val(),
                rankSep: parseInt(this.$('#ranksep').val(), 10),
                edgeSep: parseInt(this.$('#edgesep').val(), 10),
                nodeSep: parseInt(this.$('#nodesep').val(), 10)
            };
        },

        buildGraphFromAdjacencyList: function(adjacencyList) {

            var elements = [];
            var links = [];

            Object.keys(adjacencyList).forEach(function(parentLabel) {
                // Add element
                elements.push(
                    new Shape({ id: parentLabel }).setText(parentLabel)
                );
                // Add links
                adjacencyList[parentLabel].forEach(function(childLabel) {
                    links.push(
                        new Link()
                            .connect(parentLabel, childLabel)
                    );
                });
            });

            // Links must be added after all the elements. This is because when the links
            // are added to the graph, link source/target
            // elements must be in the graph already.
            return elements.concat(links);
        }

    });

    var LinkControls = joint.mvc.View.extend({

        highlighter: {
            name: 'stroke',
            options: {
                attrs: {
                    'stroke': 'lightcoral',
                    'stroke-width': 4
                }
            }
        },

        events: {
            change: 'updateLink',
            input: 'updateLink'
        },

        init: function() {
            this.highlight();
            this.updateControls();
        },

        updateLink: function() {
            this.options.cellView.model.set(this.getModelAttributes(), { layout: true });
        },

        updateControls: function() {

            var link = this.options.cellView.model;

            this.$('#labelpos').val(link.get('labelPosition'));
            this.$('#labeloffset').val(link.get('labelOffset'));
            this.$('#minlen').val(link.get('minLen'));
            this.$('#weight').val(link.get('weight'));
        },

        getModelAttributes: function() {
            return {
                minLen: parseInt(this.$('#minlen').val(), 10),
                weight: parseInt(this.$('#weight').val(), 10),
                labelPosition: this.$('#labelpos').val(),
                labelOffset: parseInt(this.$('#labeloffset').val(), 10)
            };
        },

        onRemove: function() {
            this.unhighlight();
        },

        highlight: function() {
            this.options.cellView.highlight('rect', { highlighter: this.highlighter });
        },

        unhighlight: function() {
            this.options.cellView.unhighlight('rect', { highlighter: this.highlighter });
        }

    }, {

        create: function(linkView) {
            this.remove();
            this.instance = new this({
                el: this.template.cloneNode(true).getElementById('link-controls'),
                cellView: linkView
            });
            this.instance.$el.insertAfter('#layout-controls');
        },

        remove: function() {
            if (this.instance) {
                this.instance.remove();
                this.instance = null;
            }
        },

        refresh: function() {
            if (this.instance) {
                this.instance.unhighlight();
                this.instance.highlight();
            }
        },

        instance: null,

        template: document.getElementById('link-controls-template').content

    });

    var controls = new LayoutControls({
        el: document.getElementById('layout-controls'),
        paper: new joint.dia.Paper({
            el: document.getElementById('paper'),
            interactive: function(cellView) {
                return cellView.model.isElement();
            }
        }).on({
            'link:pointerdown': LinkControls.create,
            'blank:pointerdown element:pointerdown': LinkControls.remove
        }, LinkControls),
        adjacencyList: {
            a: ['b','c','d'],
            b: ['d', 'e'],
            c: [],
            d: [],
            e: ['e'],
            f: [],
            g: ['b','i'],
            h: ['f'],
            i: ['f','h']
        }
    }).on({
        'layout': LinkControls.refresh
    }, LinkControls);

    controls.layout();

</script>
@endsection
