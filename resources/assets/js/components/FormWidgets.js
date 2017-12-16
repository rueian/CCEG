import React from 'react';

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

export default {
    columnSelector: ColumnSelector
};