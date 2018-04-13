@extends('main')

@section('jumbotron')
    <div class="jumbotron jumbotron-fluid">
        <div class="container">
            <h1 class="display-3">運算流程藍圖列表</h1>
            <p class="lead">欲使用此平台，請先新增一個流程藍圖</p>
        </div>
    </div>
@endsection

@section('container')
    <div class="card-deck row">
        <div class="col-xl-3 col-md-4 col-sm-6 col-12">
            <div class="card mb-3 mr-0 ml-0 mb-3">
                <a href="{{ url('/blueprints') }}" data-remote="true" data-method="POST" class="btn btn-light text-secondary" style="min-height: 15rem; font-size: 3rem;">
                    <span style="display: block; margin-top: 4.5rem">
                        <i class="fas fa-plus-circle"></i>
                        新增藍圖
                    </span>
                </a>
            </div>
        </div>

        @foreach($blueprints as $blueprint)
            <div class="col-xl-3 col-md-4 col-sm-6 col-12">
                <div class="card mb-3 mr-0 ml-0" style="min-height: 15rem;">
                    <div class="card-body">
                        <h4 class="card-title">{{ $blueprint->name }}</h4>
                        <p class="card-text">{{ $blueprint->note }}</p>
                    </div>
                    <div class="card-footer bg-transparent border-top-0">
                        <div class="btn-toolbar float-right">
                            <div class="btn-group mr-2">
                                <a href="{{ url('/blueprints/'.$blueprint->id.'/edit') }}" class="btn btn-sm btn-primary">編輯藍圖</a>
                            </div>
                            <div class="btn-group">
                                <a href="{{ url('/blueprints/'.$blueprint->id) }}" data-remote="true" data-method="delete" data-confirm="確定要刪除嗎？所有資料包含執行副本均會移除" class="btn btn-sm btn-danger">刪除</a>
                            </div>
                        </div>
                    </div>
                </div>
            </div>
        @endforeach
    </div>
@endsection
