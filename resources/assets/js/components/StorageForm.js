import React, { Component } from 'react';
import ReactDOM from 'react-dom';
import Form from "react-jsonschema-form";
import {refreshPage, handleAxiosError} from "../axios-handler";
import FormWidgets from "./FormWidgets";
import FormFields from "./FormFields";
import Bootstrap4ArrayFieldTemplate from "./BS4ArrayFieldTemplate";

export default class StorageForm extends Component {
    constructor(props) {
        super(props);

        this.state = {
            type: ''
        };
    }

    handleOnSubmit(e) {
        let id = this.props.blueprint.id;

        e.formData.type = this.state.type;

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
            form = <Form {...formSchema[this.state.type]} widgets={FormWidgets} fields={FormFields} ArrayFieldTemplate={Bootstrap4ArrayFieldTemplate} onSubmit={this.handleOnSubmit.bind(this)}>
                <button className="btn btn-info" type="submit">送出</button>
            </Form>
        }

        return (
            <div>
                <form>
                    <div className="form-group">
                        <label>選擇資料源類別</label>
                        <select className="form-control form-control-lg" onChange={this.handleTypeChange.bind(this)}>
                            <option key="empty" value="" />
                            {Object.keys(formSchema).filter((k) => {
                                return formSchema[k].userCreatable
                            }).map((k, i) => (
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
