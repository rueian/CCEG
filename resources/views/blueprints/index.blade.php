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
  <div class="col-md-4 col-sm-6 col-xs-12">
    <a href="{{ url('/blueprints') }}" data-remote="true" data-method="POST" class="btn btn-lg btn-light btn-block border-secondary mb-3" style="min-height: 15rem; display: table;">
      <div class="card text-center bg-transparent border-0" style="display: table-cell; vertical-align: middle;">
        <div class="card-body text-center">
          <p class="card-text text-secondary" style="font-size: 3rem;">
            新增藍圖
          </p>
        </div>
      </div>
    </a>
  </div>

  @foreach($blueprints as $blueprint)
  <div class="col-md-4 col-sm-6 col-xs-12">
    <div class="card border-secondary mb-3" style="min-height: 15rem;">
      <div class="card-body">
        <h4 class="card-title">{{ $blueprint->name }}</h4>
        <p class="card-text">
          {{ $blueprint->note }}
        </p>
        <a href="#" class="btn btn-lg btn-primary" style="bottom: -4rem; position: relative;">進入</a>
      </div>
    </div>
  </div>
  @endforeach
</div>

@endsection
