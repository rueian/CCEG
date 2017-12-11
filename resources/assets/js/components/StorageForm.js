import React, { Component } from 'react';
import ReactDOM from 'react-dom';
import Form from "react-jsonschema-form";

export default class StorageForm extends Component {
    constructor(props) {
        super(props);

        this.state = {
            type: ''
        };
    }

    handleOnSubmit(e) {

    };

    handleTypeChange(e) {
        this.setState({
            type: e.target.value
        });
    };

    render() {
        let form;

        if (this.state.type !== '') {
            form = <Form schema={this.props.formSchema[this.state.type].schema} onSubmit={this.handleOnSubmit.bind(this)} />
        }

        return (
            <div>
                <form>
                    <div className="form-group">
                        <label>選擇資料源類別</label>
                        <select className="form-control form-control-lg" onChange={this.handleTypeChange.bind(this)}>
                            <option key="empty" value="" />
                            {Object.keys(this.props.formSchema).map((k, i) => (
                                <option key={k} value={k}>{this.props.formSchema[k].name}</option>
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
    ReactDOM.render(<StorageForm formSchema={window.StorageFormSchema} />, document.getElementById('storageForm'));
}
