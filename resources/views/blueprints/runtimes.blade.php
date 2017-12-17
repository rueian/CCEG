@extends('main')

@section('jumbotron')
    <div class="jumbotron">
        <div class="container">
            <h1 class="display-3">
                {{ $blueprint->name }}
            </h1>
            <p class="lead">
                {{ $blueprint->note }}
            </p>
        </div>
    </div>
@endsection

@section('container')
    <div class="row">
        <div class="col-md-2">
            <ul class="list-group">
                <a href="{{ url('/blueprints/' . $blueprint->id . '/edit') }}" class="list-group-item">
                    <span class="fa fa-arrow-left"></span>
                    返回藍圖
                </a>
                @foreach($runtimes as $r)
                    <a href="{{ url('/blueprints/' . $blueprint->id . '/runtimes?runtime_id=' . $r->id) }}" class="list-group-item {{ $runtime && $r->id == $runtime->id ? 'active' : '' }}">
                        編號:{{ $r->id }}
                        <br>
                        {{ $r->created_at }}
                    </a>
                @endforeach
            </ul>
        </div>
        <div class="col-md-10">
            <div class="row">
                <div class="col-md-12" style="display:none;">
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
        </div>
    </div>

    <style>
        #paper {
            position: absolute;
            margin-left: auto;
            margin-right: auto;
            left: 0;
            right: 0;
            top: 10px;
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
            runtime: @json($runtime),
        };
    </script>
@endsection

@section('afterScript')
    <script>
        var Shape = joint.dia.Element.define('demo.Shape', {
            size: {
                width: 150,
                height: 80
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
                    fontSize: 15
                }
            }
        }, {
            markup: '<rect/><text/>',

            setText: function(text) {
                return this.attr('text/text', text || '');
            }
        });

        var GeneratedShape = joint.dia.Element.define('demo.GeneratedShape', {
            size: {
                width: 150,
                height: 80
            },
            attrs: {
                rect: {
                    refWidth: '100%',
                    refHeight: '100%',
                    fill: '#B0E0E6',
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
                    fontSize: 15
                }
            }
        }, {
            markup: '<rect/><text/>',

            setText: function(text) {
                return this.attr('text/text', text || '');
            }
        });

        var StepShape = joint.dia.Element.define('demo.StepShape', {
            size: {
                width: 200,
                height: 100
            },
            attrs: {
                rect: {
                    refWidth: '100%',
                    refHeight: '100%',
                    fill: '#F0FFFF',
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
                    fontSize: 15
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
            labels: [{
                markup: '<rect/><text/>',
                attrs: {
                    text: {
                        fill: 'gray',
                        refY: '50%',
                        textAnchor: 'middle',
                        refY2: '-50%',
                        fontSize: 10,
                        yAlignment: 'middle',
                        xAlignment: 'middle',
                        cursor: 'pointer'
                    },
                    rect: {
                        fill: 'lightgray',
                        stroke: 'gray',
                        strokeWidth: 2,
                        refWidth: '100%',
                        refHeight: '100%',
                        refX: '-50%',
                        refY: '-50%',
                        rx: 5,
                        ry: 5
                    }
                },
                size: {
                    width: 50, height: 30
                }
            }]

        }, {
            markup: '<path class="connection"/><g class="labels"/>',

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
                padding: 10
            },

            init: function() {

                var options = this.options;
                if (window.Props.runtime) {
                    options.cells = this.buildGraphFromBlueprint(window.Props.runtime);
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

            buildGraphFromBlueprint: function(blueprint) {

                var elements = [];
                var links = [];

                if (blueprint.payload && blueprint.payload.storages) {
                    Object.keys(blueprint.payload.storages).forEach(function(key) {
                        var storage = blueprint.payload.storages[key];

                        if (storage.generated) {
                            elements.push(new GeneratedShape({ id: key, payload: storage }).setText(storage.name));
                        } else {
                            elements.push(new Shape({ id: key, payload: storage }).setText('資料源 ' + storage.name));
                        }
                    });
                }

                if (blueprint.payload && blueprint.payload.steps) {
                    Object.keys(blueprint.payload.steps).forEach(function(key) {
                        var step = blueprint.payload.steps[key];
                        elements.push(
                            new StepShape({ id: key, payload: step }).setText('步驟 ' + step.name)
                        );

                        Object.keys(step.inputs).forEach(function(input) {
                            let labelMap = {
                                'input': '輸入',
                                'semi': '篩選',
                                'left': '左方',
                                'right': '右方'
                            };
                            let label = input;
                            if (labelMap[input]) {
                                label = labelMap[input];
                            }

                            links.push(
                                new Link()
                                    .connect(step.inputs[input], key)
                                    .setLabelText(label)
                            );
                        });

                        links.push(
                            new Link()
                                .connect(key, step.output)
                                .setLabelText('輸出')
                        );
                    });
                }

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
                'blank:pointerdown element:pointerdown': LinkControls.remove,
                'cell:pointerclick': function(cellView, evt, x, y) {

                    if (cellView.model.attributes.payload) {
                        let target = cellView.model.attributes.payload;

                        let titlePrefix = '';
                        if (window.Props.stepFormSchema[target.type]) {
                            titlePrefix = '步驟 ';
                        }
                        if (window.Props.storageFormSchema[target.type]) {
                            titlePrefix = '資料源 ';
                        }

                        let $previewModel = $('#previewModal');

                        $previewModel.find('#previewModalLabel').text(titlePrefix + target.name);
                        $previewModel.find('#previewModalForm').empty();

                        window.ReactDOM.render(
                            window.React.createElement(
                                window.PreviewForm,
                                {
                                    target: target,
                                    targetKey: cellView.model.id,
                                    blueprint: window.Props.blueprint,
                                    stepFormSchema: window.Props.stepFormSchema,
                                    storageFormSchema: window.Props.storageFormSchema
                                },
                            ),
                            document.getElementById('previewModalForm'),
                        );

                        $previewModel.modal('show');
                    }
                }
            }, LinkControls),
        }).on({
            'layout': LinkControls.refresh
        }, LinkControls);

        controls.layout();

    </script>
@endsection