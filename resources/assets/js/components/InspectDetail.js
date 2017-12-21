import React, { Component } from 'react';
import XLSX from 'xlsx';
import PreviewForm from './PreviewForm';
import HotTable from 'react-handsontable';

export default class InspectDetail extends Component {
    constructor(props) {
        super(props);
        this.state = {
            workbook: {},
            selectSheet: '',
            parsing: false,
            parseErrMsg: '',
            data: []
        };
    }

    handleFileSelected(e) {
        let file = this.refs.fileInput.files[0];

        if (!file) { return }

        this.setState({
            ...this.state,
            parsing: true,
            parseErrMsg: '',
            workbook: {}
        });

        let reader = new FileReader();

        reader.onload = (e) => {
            try {
                let data = new Uint8Array(e.target.result);
                let workbook = XLSX.read(data, {type: 'array'});

                this.setState({
                    ...this.state,
                    workbook: workbook,
                    data: [],
                    parsing: false,
                    parseErrMsg: '',
                });
            } catch(err) {
                console.log(err);
                this.setState({
                    ...this.state,
                    parsing: false,
                    parseErrMsg: err.message,
                });
            }
        };

        reader.readAsArrayBuffer(file);
    }

    handleSheetSelected(e) {
        let selectSheet = e.target.value;

        if (!selectSheet) {
            this.setState({
                ...this.state,
                selectSheet: '',
                data: []
            });
            return
        }

        let sheet = this.state.workbook.Sheets[selectSheet];

        let data = XLSX.utils.sheet_to_json(sheet, {header:1});

        this.setState({
            ...this.state,
            selectSheet: selectSheet,
            data: data
        });
    }

    render() {

        let target = this.props.target;

        let body = null;
        let stateAlert = null;
        if (this.props.stepFormSchema[target.type]) {
            body = <PreviewForm {...this.props}/>;
            if (target.state === 'error') {
                stateAlert = <div className="alert alert-danger">執行錯誤：{target.error.message}</div>
            } else if (target.state === 'done') {
                stateAlert = <div className="alert alert-success">執行正常結束</div>
            } else {
                stateAlert = <div className="alert alert-warning">尚未執行</div>
            }
        } else if (this.props.storageFormSchema[target.type]) {
            body = (
                <div>
                    <PreviewForm {...this.props}/>
                    <hr/>
                    <h3>資料上傳</h3>
                    <form>
                        <div className="form-group">
                            <input type="file" ref="fileInput" onChange={this.handleFileSelected.bind(this)} />
                            {
                                (this.state.parsing) ? <p className="help-block">解析中...</p> : <div/>
                            }
                            {
                                (this.state.parseErrMsg) ? <p className="text-danger">解析失敗：{this.state.parseErrMsg}</p> : <div/>
                            }
                        </div>
                        {
                            (this.state.workbook.SheetNames && this.state.workbook.SheetNames.length > 0) ? (
                                <div className="form-group">
                                    <label>選擇表格</label>
                                    <select className="form-control form-control-lg" onChange={this.handleSheetSelected.bind(this)}>
                                        <option key="empty" value="" />
                                        {this.state.workbook.SheetNames.map((v) => (
                                            <option key={v} value={v}>{v}</option>
                                        ))}
                                    </select>
                                </div>
                            ) : <div/>
                        }
                        {
                            (this.state.data.length > 0) ? (
                                <div className="form-group">
                                    <label>指定欄位名稱</label>
                                    <p className="help-block">請將上方資料源定義的欄位名稱 ({target.schema.map((s) => s.name).join(', ')}) 填入下方表格預覽中的第一列，以標明對應的欄位位置</p>
                                    <div style={{ overflow: 'hidden'}}>
                                        <HotTable root="hot" settings={{
                                            data: this.state.data.slice(0, 5),
                                            colHeaders: false,
                                            rowHeaders: true,
                                            height: 120,
                                            cells: function(row, col, prop) {
                                                return {
                                                    readOnly: row > 0
                                                };
                                            }
                                        }}/>
                                    </div>
                                </div>
                            ) : <div />
                        }
                        {
                            (this.state.data.length > 0) ? (
                                <button className="btn btn-default" type="submit">上傳</button>
                            ) : <div />
                        }
                    </form>
                </div>
            );
            if (target.state === 'error') {
                stateAlert = <div className="alert alert-danger">上傳錯誤：{target.error.message}</div>
            } else if (target.state === 'done') {
                stateAlert = <div className="alert alert-success">資料已上傳</div>
            } else {
                stateAlert = <div className="alert alert-warning">資料尚未上傳</div>
            }
        }

        return (
            <div>
                { stateAlert }
                { body }
            </div>
        )
    }
}