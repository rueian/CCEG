import React, { Component } from 'react';
import Form from "react-jsonschema-form";
import {refreshPage, handleAxiosError} from "../axios-handler";
import FormWidgets from "./FormWidgets";

export default class PreviewForm extends Component {
    handleOnDelete(e) {
        let id = this.props.blueprint.id;
        let target = this.props.target;

        let url = '';
        if (this.props.stepFormSchema[target.type]) {
            url = `/blueprints/${id}/step/${this.props.targetKey}`;
        } else {
            url = `/blueprints/${id}/storage/${this.props.targetKey}`;
        }

        axios.delete(url).then(refreshPage).catch(handleAxiosError);
    };

    render() {
        let target = this.props.target;
        let schema = {};

        if (this.props.stepFormSchema[target.type]) {
            schema = window.Props.stepFormSchema[target.type];
        }
        if (this.props.storageFormSchema[target.type]) {
            schema = window.Props.storageFormSchema[target.type];
        }

        let formSchema = JSON.parse(JSON.stringify(schema.schema));
        let formUISchema = JSON.parse(JSON.stringify(schema.uiSchema));
        formUISchema['ui:readonly'] = true;

        let deleteBtn = <button className="btn btn-danger" onClick={this.handleOnDelete.bind(this)}>刪除</button>;

        return (
            <Form
                formData={target}
                formContext={target}
                schema={formSchema}
                uiSchema={formUISchema}
                widgets={FormWidgets}
            >
                { this.props.noDelete ? <div/> : deleteBtn }
            </Form>
        );
    }
};