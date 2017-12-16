import React, { Component } from 'react';
import ReactDOM from 'react-dom';
import Form from "react-jsonschema-form";
import {refreshPage, handleAxiosError} from "../axios-handler";

const ColumnSelector = (props) => {
    let options = props.options;
    let formData = props.formContext;

    let schema = [];
    if (options && options.inputKey) {
        if (formData.inputs && formData.inputs[options.inputKey]) {
            let storage = window.Props.blueprint.payload.storages[formData.inputs[options.inputKey]];
            schema = storage.schema;
        }
    }

    return (
        <select className="form-control"
                value={props.value}
                required={props.required}
                onChange={(event) => props.onChange(event.target.value)}
                disabled={props.readonly || props.disabled}
        >
            <option key={'empty'} value={''} />
            { schema.map(column => (
                <option key={Math.random().toString(36).substring(2, 10)} value={column.name}>{column.name}</option>
            )) }
        </select>
    );
};

window.FormWidgets = {
    columnSelector: ColumnSelector
};

export default class StepForm extends Component {
    constructor(props) {
        super(props);

        this.state = {
            type: '',
            formData: {}
        };
    }

    handleOnSubmit(e) {
        let id = this.props.blueprint.id;

        e.formData.type = this.state.type;

        axios.post(`/blueprints/${id}/step`, e.formData)
            .then(refreshPage)
            .catch(handleAxiosError);
    };

    handleTypeChange(e) {
        this.setState({
            ...this.state,
            type: e.target.value
        });
    };

    handleFormDataChange(e) {
        this.setState({
            ...this.state,
            formData: e.formData
        });
    }

    render() {
        let form;
        let formSchema = this.props.stepFormSchema;

        if (this.state.type !== '') {
            form = <Form {...formSchema[this.state.type]} formContext={this.state.formData} formData={this.state.formData} widgets={window.FormWidgets} onChange={this.handleFormDataChange.bind(this)} onSubmit={this.handleOnSubmit.bind(this)} />
        }

        return (
            <div>
                <form>
                    <div className="form-group">
                        <label>選擇步驟累別</label>
                        <select className="form-control form-control-lg" onChange={this.handleTypeChange.bind(this)}>
                            <option key="empty" value="" />
                            {Object.keys(formSchema).map((k, i) => (
                                <option key={k} value={k}>{formSchema[k].name}</option>
                            ))}
                        </select>
                    </div>
                </form>

                {form}
            </div>
        );
    }
}

if (document.getElementById('stepForm')) {
    ReactDOM.render(<StepForm {...window.Props} />, document.getElementById('stepForm'));
}
