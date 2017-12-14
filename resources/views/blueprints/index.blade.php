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

<div class="row">
  <div class="col-md-3 col-sm-6 col-xs-12">
    <a href="{{ url('/blueprints') }}" data-remote="true" data-method="POST" class="btn btn-lg btn-light btn-block border-secondary mb-3" style="min-height: 15rem; display: table">
      <div class="" style="display: table-cell; vertical-align: middle;">
        <div class="panel-body text-center">
          <span class="panel-text text-secondary" style="font-size: 4rem;">
            <i class="fas fa-plus-circle"></i>
            新增藍圖
          </span>
        </div>
      </div>
    </a>
  </div>

  @foreach($blueprints as $blueprint)
  <div class="col-md-3 col-sm-6 col-xs-12">
    <div class="panel panel-default" style="min-height: 15rem;">
      <div class="panel-heading">
        {{ $blueprint->name }}
        <a href="{{ url('/blueprints/'.$blueprint->id.'/edit') }}" class="btn btn-sm btn-primary pull-right" style="bottom: 5px; position: relative;">進入</a>
      </div>
      <div class="panel-body">
        <p class="panel-text">
          {{ $blueprint->note }}
        </p>
      </div>
    </div>
  </div>
  @endforeach
</div>

@endsection
