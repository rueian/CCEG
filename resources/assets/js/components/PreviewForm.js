import React, { Component } from 'react';
import Form from "react-jsonschema-form";
import {refreshPage, handleAxiosError} from "../axios-handler";
import FormWidgets from "./FormWidgets";

export default class PreviewForm extends Component {
    handleOnDelete(e) {
        let id = this.props.blueprint.id;

        e.formData.type = this.state.type;

        axios.post(`/blueprints/${id}/step`, e.formData)
            .then(refreshPage)
            .catch(handleAxiosError);
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

        return (
            <Form
                formData={target}
                formContext={target}
                schema={formSchema}
                uiSchema={formUISchema}
                widgets={FormWidgets}
            >
                <div />
            </Form>
        );
    }
};