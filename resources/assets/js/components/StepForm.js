import React, { Component } from 'react';
import ReactDOM from 'react-dom';
import Form from "react-jsonschema-form";

export default class StepForm extends Component {
    render() {
        return (
            <div className="container">
                <div className="row">
                    <div className="col-md-8 col-md-offset-2">
                        <div className="panel panel-default">
                            <div className="panel-heading">Example Component</div>

                            <div className="panel-body">
                                I'm an example component!
                            </div>
                        </div>
                    </div>
                </div>
            </div>
        );
    }
}

if (document.getElementById('stepForm')) {
    ReactDOM.render(<StepForm />, document.getElementById('stepForm'));
}
