import React, { Component } from 'react';
import Form from "react-jsonschema-form";
import {refreshPage, handleAxiosError} from "../axios-handler";
import FormWidgets from "./FormWidgets";
import FormFields from "./FormFields";
import Bootstrap4ArrayFieldTemplate from "./BS4ArrayFieldTemplate";

export default class PreviewForm extends Component {
    handleOnDelete(e) {
        e.preventDefault(); // avoid trigger handleOnSubmit
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

    handleOnSubmit(e) {
        console.log('onsubmit', e);
        let id = this.props.blueprint.id;
        let target = this.props.target;

        let url = '';
        if (this.props.stepFormSchema[target.type]) {
            url = `/blueprints/${id}/step/${this.props.targetKey}`;
        } else {
            url = `/blueprints/${id}/storage/${this.props.targetKey}`;
        }

        axios.put(url, e.formData).then(refreshPage).catch(handleAxiosError);
    }

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

        if (this.props.stepFormSchema[target.type]) {
            if (!formUISchema['inputs']) {
                formUISchema['inputs'] = {};
            }
            formUISchema['inputs']['ui:readonly'] = true;

            if (target.type == 'sql_select_map') {
                formUISchema['param']['select']['ui:options'] = {removable: false};
            }
            if (target.type == 'sql_group_by') {
                formUISchema['param']['group']['ui:options'] = {removable: false};
                formUISchema['param']['select']['ui:options'] = {removable: false};
            }
        }
        if (this.props.noDelete || this.props.storageFormSchema[target.type]) {
            formUISchema['ui:readonly'] = true;
        }

        let updateBtn;
        if (this.props.stepFormSchema[target.type]) {
            updateBtn = <button className="btn btn-info" type="submit">更新</button>;
        } else {
            updateBtn = <div/>;
        }

        let deleteBtn = <button className="btn btn-danger float-right" onClick={this.handleOnDelete.bind(this)}>刪除</button>;

        return (
            <Form
                formData={target}
                formContext={target}
                schema={formSchema}
                uiSchema={formUISchema}
                widgets={FormWidgets}
                fields={FormFields}
                ArrayFieldTemplate={Bootstrap4ArrayFieldTemplate}
                onSubmit={this.handleOnSubmit.bind(this)}
            >
                { this.props.noDelete ? <div/> : updateBtn }
                { this.props.noDelete ? <div/> : deleteBtn }
            </Form>
        );
    }
};