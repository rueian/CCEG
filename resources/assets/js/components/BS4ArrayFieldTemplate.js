import React from "react";

function AddButton({ onClick, disabled }) {
    return (
        <div className="row">
            <p className="col-2 offset-10 array-item-add text-right">
                <IconBtn
                    type="info"
                    icon="plus"
                    className="btn-add col-12"
                    tabIndex="0"
                    onClick={onClick}
                    disabled={disabled}
                />
            </p>
        </div>
    );
}

function ArrayFieldTitle({ TitleField, idSchema, title, required }) {
    if (!title) {
        // See #312: Ensure compatibility with old versions of React.
        return <div />;
    }
    const id = `${idSchema.$id}__title`;
    return <TitleField id={id} title={title} required={required} />;
}

function ArrayFieldDescription({ DescriptionField, idSchema, description }) {
    if (!description) {
        // See #312: Ensure compatibility with old versions of React.
        return <div />;
    }
    const id = `${idSchema.$id}__description`;
    return <DescriptionField id={id} description={description} />;
}

function IconBtn(props) {
    const { type = "default", icon, className, ...otherProps } = props;
    return (
        <button
            type="button"
            className={`btn btn-${type} ${className}`}
            {...otherProps}>
            <i className={`fas fa-${icon}`} />
        </button>
    );
}

// Used in the two templates
function DefaultArrayItem(props) {
    const btnStyle = {
        flex: 1,
        paddingLeft: 6,
        paddingRight: 6,
        fontWeight: "bold",
    };

    if (props.children.props.schema.type === 'object') {
        btnStyle.marginTop = '2rem';
    }

    return (
        <div key={props.index} className="row">
            <div className={props.hasToolbar ? "col-10" : "col-12"}>
                {props.children}
            </div>

            {props.hasToolbar && (
                <div className="col-2 array-item-toolbox">
                    <div
                        className="btn-group"
                        style={{ display: "flex", justifyContent: "space-around" }}>
                        {(props.hasMoveUp || props.hasMoveDown) && (
                            <IconBtn
                                icon="arrow-up"
                                className="array-item-move-up"
                                type="secondary"
                                tabIndex="-1"
                                style={btnStyle}
                                disabled={props.disabled || props.readonly || !props.hasMoveUp}
                                onClick={props.onReorderClick(props.index, props.index - 1)}
                            />
                        )}

                        {(props.hasMoveUp || props.hasMoveDown) && (
                            <IconBtn
                                icon="arrow-down"
                                className="array-item-move-down"
                                type="secondary"
                                tabIndex="-1"
                                style={btnStyle}
                                disabled={
                                    props.disabled || props.readonly || !props.hasMoveDown
                                }
                                onClick={props.onReorderClick(props.index, props.index + 1)}
                            />
                        )}

                        {props.hasRemove && (
                            <IconBtn
                                type="danger"
                                icon="minus"
                                className="array-item-remove"
                                tabIndex="-1"
                                style={btnStyle}
                                disabled={props.disabled || props.readonly}
                                onClick={props.onDropIndexClick(props.index)}
                            />
                        )}
                    </div>
                </div>
            )}
        </div>
    );
}

export default function Bootstrap4ArrayFieldTemplate(props) {
    return (
        <fieldset className={props.className}>
            <ArrayFieldTitle
                key={`array-field-title-${props.idSchema.$id}`}
                TitleField={props.TitleField}
                idSchema={props.idSchema}
                title={props.uiSchema["ui:title"] || props.title}
                required={props.required}
            />

            {(props.uiSchema["ui:description"] || props.schema.description) && (
                <ArrayFieldDescription
                    key={`array-field-description-${props.idSchema.$id}`}
                    DescriptionField={props.DescriptionField}
                    idSchema={props.idSchema}
                    description={
                        props.uiSchema["ui:description"] || props.schema.description
                    }
                />
            )}

            <div
                className="array-item-list"
                key={`array-item-list-${props.idSchema.$id}`}>
                {props.items && props.items.map(p => DefaultArrayItem(p))}
            </div>

            {props.canAdd && (
                <AddButton
                    onClick={props.onAddClick}
                    disabled={props.disabled || props.readonly}
                />
            )}
        </fieldset>
    );
}