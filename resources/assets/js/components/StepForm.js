import React, { Component } from 'react';
import ReactDOM from 'react-dom';
import Form from "react-jsonschema-form";
import {refreshPage, handleAxiosError} from "../axios-handler";
import FormWidgets from "./FormWidgets";

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
            form = <Form {...formSchema[this.state.type]} formContext={this.state.formData} formData={this.state.formData} widgets={FormWidgets} onChange={this.handleFormDataChange.bind(this)} onSubmit={this.handleOnSubmit.bind(this)}>
                <button className="btn btn-info" type="submit">送出</button>
            </Form>
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
