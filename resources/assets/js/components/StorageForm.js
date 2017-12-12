import React, { Component } from 'react';
import ReactDOM from 'react-dom';
import Form from "react-jsonschema-form";
import {refreshPage, handleAxiosError} from "../axios-handler";

export default class StorageForm extends Component {
    constructor(props) {
        super(props);

        this.state = {
            type: ''
        };
    }

    handleOnSubmit(e) {
        let id = this.props.blueprint.id;

        axios.post(`/blueprints/${id}/storage`, e.formData)
            .then(refreshPage)
            .catch(handleAxiosError);
    };

    handleTypeChange(e) {
        this.setState({
            type: e.target.value
        });
    };

    render() {
        let form;
        let formSchema = this.props.storageFormSchema;

        if (this.state.type !== '') {
            form = <Form schema={formSchema[this.state.type].schema} onSubmit={this.handleOnSubmit.bind(this)} />
        }

        return (
            <div>
                <form>
                    <div className="form-group">
                        <label>選擇資料源類別</label>
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

if (document.getElementById('storageForm')) {
    ReactDOM.render(<StorageForm {...window.Props} />, document.getElementById('storageForm'));
}
