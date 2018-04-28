import React from 'react';

class ColumnCreator extends React.Component {
    constructor(props) {
        super(props);
        this.state = {...props.formData};
        if (!this.state.name) {
            this.state.name = '';
        }
        if (!this.state.type) {
            this.state.type = '';
        }
    }

    componentWillReceiveProps(nextProps) {
        if (nextProps.formData) {
            this.setState({
                ...nextProps.formData
            });
        }
    }

    onChange(name) {
        return (event) => {
            this.setState({
                [name]: event.target.value
            }, () => this.props.onChange(this.state));
        };
    }

    render() {
        const state = this.state;
        const props = this.props;

        const schema = this.props.schema;
        const fields = this.props.schema.properties;

        const onChange = this.onChange.bind(this);

        let size = 12 / (Object.keys(fields).length || 1);
        let className = 'col-' + size;

        return (
            <div className="row">
                {
                    Object.keys(fields).map(function (k) {
                        return (
                            <div className={className} key={k}>
                                <div className="form-group">
                                    <label>{fields[k].title}{schema.required.indexOf(k) !== -1 ? '*' : ''}</label>
                                    {
                                        (fields[k].enum) ? (
                                            <select className="form-control" value={state[k] || ''} required={schema.required.indexOf(k) !== -1} disabled={props.readonly || props.disabled} onChange={onChange(k)}>
                                                <option value={''} />
                                                {
                                                    (fields[k].enum.map(function(v, i) {
                                                        return <option key={v} value={v}>{fields[k].enumNames[i]}</option>
                                                    }))
                                                }
                                            </select>
                                        ) : <input className="form-control" type="text" value={state[k] || ''} required={schema.required.indexOf(k) !== -1} disabled={props.readonly || props.disabled} onChange={onChange(k)}/>
                                    }
                                </div>
                            </div>
                        )
                    })
                }
            </div>
        )
    }
};

export default {
    columnCreator: ColumnCreator
};