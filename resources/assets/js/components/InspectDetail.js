import React, { Component } from 'react';
import XLSX from 'xlsx';
import PreviewForm from './PreviewForm';
import HotTable from 'react-handsontable';
import FileSaver from 'file-saver';
import {handleAxiosError, refreshPage} from "../axios-handler";

export default class InspectDetail extends Component {
    constructor(props) {
        super(props);
        this.state = {
            workbook: {},
            selectSheet: '',
            parsing: false,
            parseErrMsg: '',
            data: [],
            downloading: true,
            export: []
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

    handleSubmit(e) {
        e.preventDefault();

        let headerRow = this.state.data[0];
        let targetFields = this.props.target.schema.map((s) => s.name);

        let fieldMap = {};

        for(let field of targetFields) {
            let i = headerRow.indexOf(field);
            if (i !== -1) {
                fieldMap[field] = i;
            }
        }

        let selectedField = Object.keys(fieldMap);
        if (selectedField.length === 0) {
            alert('預覽表格中的第一列不包含任何儲存空間定義的欄位名稱 (' + targetFields.join(', ') + ')');
            return;
        }

        let submitData = [];

        for (let row of this.state.data) {
            let submitRow = [];
            for (let field of selectedField) {
                submitRow.push(row[fieldMap[field]]);
            }
            submitData.push(submitRow);
        }

        let storage = window.Props.storages[this.props.targetKey];

        axios.post(`/storages/${storage.id}/import`, {
            data: submitData
        }).then(refreshPage).catch(handleAxiosError);
    }

    componentDidMount() {
        let storage = window.Props.storages[this.props.targetKey];
        if (storage && storage.state === 'done') {
            this.setState({
                ...this.state,
                downloading: true,
            });
            axios.get(`/storages/${storage.id}/export`).then((res) => {
                // wait to avoid HotTable rendering before modal show up
                setTimeout(() => {
                    this.setState({
                        ...this.state,
                        downloading: false,
                        export: res.data.data,
                    })
                }, 1000);
            }).catch(handleAxiosError);
        }
    }

    handleDownload() {
        try {
            let sheet = XLSX.utils.aoa_to_sheet(this.state.export);

            let workbook = {
                SheetNames: [this.props.targetKey],
                Sheets: {}
            };
            workbook.Sheets[this.props.targetKey] = sheet;

            let wopts = { bookType: 'xlsx', type:'binary' };
            let wbout = XLSX.write(workbook, wopts);

            FileSaver.saveAs(new Blob([this.s2ab(wbout)], {type: 'application/octet-stream'}), this.props.targetKey + '.xlsx');
        } catch (err) {
            alert('下載失敗： ' + err.message);
        }
    }

    s2ab(s) {
        let buf = new ArrayBuffer(s.length);
        let view = new Uint8Array(buf);
        for (let i=0; i !== s.length; ++i) view[i] = s.charCodeAt(i) & 0xFF;
        return buf;
    }

    render() {

        let target = this.props.target;
        let targetKey = this.props.targetKey;

        let body = null;
        let stateAlert = null;
        let table = null;
        if (this.props.stepFormSchema[target.type]) {
            body = <PreviewForm {...this.props}/>;

            let step = window.Props.steps[targetKey];
            if (step.state === 'error') {
                stateAlert = <div className="alert alert-danger">執行錯誤：{step.error.message}</div>
            } else if (step.state === 'done') {
                stateAlert = <div className="alert alert-success">執行正常結束</div>
            } else {
                stateAlert = <div className="alert alert-warning">尚未執行</div>
            }

            if (step.type === 'smt') {
                table = (
                    <div>
                        {
                            (step.param['input']) ? (
                                <div className="form-group">
                                    <label className="control-label">SMT 原始輸入</label>
                                    <textarea className="form-control" value={step.param['input']} readOnly={true}/>
                                </div>
                            ) : <div/>
                        }
                        {
                            (step.param['output']) ? (
                                <div className="form-group">
                                    <label className="control-label">SMT 原始輸出</label>
                                    <textarea className="form-control" value={step.param['output']} readOnly={true}/>
                                </div>
                            ) : <div/>
                        }
                    </div>
                )
            }
        } else if (this.props.storageFormSchema[target.type]) {
            body = (window.Props.runtime.payload.storages[targetKey].generated) ? <PreviewForm {...this.props}/> : (
                <div>
                    <PreviewForm {...this.props}/>
                    <hr/>
                    <h3>資料上傳</h3>
                    <form onSubmit={this.handleSubmit.bind(this)}>
                        <div className="form-group">
                            <input type="file" className="form-control-file" ref="fileInput" onChange={this.handleFileSelected.bind(this)} />
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
                                    <p className="help-block">請將上方儲存空間定義的欄位名稱 ({target.schema.map((s) => s.name).join(', ')}) 填入下方表格預覽中的第一列，以標明對應的欄位位置</p>
                                    <div style={{ overflow: 'hidden'}}>
                                        <HotTable settings={{
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
                                <div className="form-group">
                                    <button className="btn btn-success" type="submit">上傳</button>
                                </div>
                            ) : <div />
                        }
                    </form>
                </div>
            );
            let storage = window.Props.storages[targetKey];
            if (storage.state === 'error') {
                stateAlert = <div className="alert alert-danger">上傳錯誤：{storage.error.message}</div>
            } else if (storage.state === 'done') {
                stateAlert = <div className="alert alert-success">資料已{window.Props.runtime.payload.storages[targetKey].generated ? '產出' : '上傳'}</div>
            } else {
                stateAlert = <div className="alert alert-warning">資料尚未{window.Props.runtime.payload.storages[targetKey].generated ? '產出' : '上傳'}</div>
            }

            if (storage.state === 'done') {
                table = (
                    <div>
                        <hr/>
                        <h3>資料瀏覽</h3>
                        {
                            (this.state.downloading) ? <div className="alert alert-warning">資料下載中...</div> : <div/>
                        }
                        {
                            (!this.state.downloading && storage.type === 'table' && this.state.export.length > 0) ? (
                                <div style={{ overflow: 'hidden'}}>
                                    <HotTable settings={{
                                        data: this.state.export,
                                        colHeaders: false,
                                        rowHeaders: true,
                                        height: 400,
                                        renderAllRows: true,
                                        cells: function(row, col, prop) {
                                            return {
                                                readOnly: true
                                            };
                                        }
                                    }}/>
                                    <div className="form-group">
                                        <button className="btn btn-info" onClick={this.handleDownload.bind(this)} style={{marginTop: '15px'}}>下載 Excel</button>
                                    </div>
                                </div>
                            ) : <textarea className="form-control" disabled={true} value={this.state.export} />
                        }
                    </div>
                );
            }
        }

        return (
            <div>
                { body }
                { stateAlert }
                { table }
            </div>
        )
    }
}