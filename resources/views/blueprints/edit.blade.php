@extends('main')

@section('jumbotron')
<div class="jumbotron">
  <div class="container">
    <h1 class="display-3">
      <a href="#" data-pk="{{ $blueprint->id }}" data-name="name" data-type="text" data-url="{{ url('/blueprints/editable') }}" data-title="流程名稱" data-editable="">{{ $blueprint->name }}</a>
    </h1>
    <p class="lead">
      <a href="#" data-pk="{{ $blueprint->id }}" data-name="note" data-type="textarea" data-url="{{ url('/blueprints/editable') }}" data-title="說明備註" data-emptytext="說明備註" data-editable="">{{ $blueprint->note }}</a>  
    </p>
  </div>
</div>
@endsection

@section('container')

<div class="row">
  <div class="col-md-2 col-sm-4 col-xs-6">
    <a href="#" data-toggle="modal" data-target="#storageModal" class="btn btn-lg btn-light btn-block border-secondary mb-3" style="min-height: 10rem; display: table;">
      <div class="card text-center bg-transparent border-0" style="display: table-cell; vertical-align: middle;">
        <div class="card-body text-center">
          <p class="card-text text-secondary" style="font-size: 2rem;">
            <i class="fas fa-plus-circle"></i>
            新增資料
          </p>
        </div>
      </div>
    </a>
  </div>

  <div class="col-md-2 col-sm-4 col-xs-6">
    <div class="card text-center border-primary mb-3" style="min-height: 10rem; max-height: 10rem; vertical-align: middle;">
      <div class="card-header">
        <i class="fas fa-archive"></i>
        資料儲存
      </div>
      <div class="card-body">
        <p class="card-text text-secondary" style="font-size: 2rem;">
          課程成績
        </p>
        <i class="fa fa-arrow-down" aria-hidden="true"></i>
      </div>
    </div>
  </div>

  <div class="col-md-2 col-sm-4 col-xs-6">
    <div class="card text-center border-primary mb-3" style="min-height: 10rem; max-height: 10rem; vertical-align: middle;">
      <div class="card-header">
        <i class="fas fa-archive"></i>
        資料儲存
      </div>
      <div class="card-body">
        <p class="card-text text-secondary" style="font-size: 2rem;">
          課程列表
        </p>
        <i class="fa fa-arrow-down" aria-hidden="true"></i>
      </div>
    </div>
  </div>

  <div class="col-md-2 col-sm-4 col-xs-6">
    <div class="card text-center border-primary mb-3" style="min-height: 10rem; max-height: 10rem; vertical-align: middle;">
      <div class="card-header">
        <i class="fas fa-archive"></i>
        資料儲存
      </div>
      <div class="card-body">
        <p class="card-text text-secondary" style="font-size: 2rem;">
          退課名單
        </p>
        <i class="fa fa-arrow-down" aria-hidden="true"></i>
      </div>
    </div>
  </div>

</div>

<div class="row">
  <div class="col-md-2 col-sm-4 col-xs-6">
    <a href="#" data-toggle="modal" data-target="#stepModal" class="btn btn-lg btn-light btn-block border-secondary mb-3" style="min-height: 10rem; display: table;">
      <div class="card text-center bg-transparent border-0" style="display: table-cell; vertical-align: middle;">
        <div class="card-body text-center">
          <p class="card-text text-secondary" style="font-size: 2rem;">
            <i class="fas fa-plus-circle"></i>
            新增運算
          </p>
        </div>
      </div>
    </a>
  </div>
  <div class="col-md-2 col-sm-4 col-xs-6">
    <div class="card text-center mb-3" style="min-height: 10rem; max-height: 10rem; vertical-align: middle;">
      <div class="card-header">
        <i class="fas fa-cogs"></i>
        SQL 運算
      </div>
      <div class="card-body">
        <p class="card-text text-secondary" style="font-size: 1.5rem;">
          篩選出必修課程
        </p>
        <i class="fa fa-arrow-down" aria-hidden="true"></i>
      </div>
    </div>
  </div>
</div>

<div class="row">
  <div class="col-md-2 col-sm-4 col-xs-6">
  </div>
  <div class="col-md-2 col-sm-4 col-xs-6">
    <div class="card text-center mb-3" style="min-height: 10rem; max-height: 10rem; vertical-align: middle;">
      <div class="card-header">
        <i class="fas fa-cogs"></i>
        SQL 運算
      </div>
      <div class="card-body">
        <p class="card-text text-secondary" style="font-size: 1.5rem;">
          算出課程成績名次
        </p>
        <i class="fa fa-arrow-down" aria-hidden="true"></i>
      </div>
    </div>
  </div>
</div>

<div class="row">
  <div class="col-md-2 col-sm-4 col-xs-6">
  </div>
  <div class="col-md-2 col-sm-4 col-xs-6">
    <div class="card text-center mb-3" style="min-height: 10rem; max-height: 10rem; vertical-align: middle;">
      <div class="card-header">
        <i class="fas fa-cogs"></i>
        SQL 運算
      </div>
      <div class="card-body">
        <p class="card-text text-secondary" style="font-size: 1.5rem;">
          分配點數
        </p>
        <i class="fa fa-arrow-down" aria-hidden="true"></i>
      </div>
    </div>
  </div>
</div>

<div class="row">
  <div class="col-md-2 col-sm-4 col-xs-6">
  </div>
  <div class="col-md-2 col-sm-4 col-xs-6">
    <div class="card text-center mb-3" style="min-height: 10rem; max-height: 10rem; vertical-align: middle;">
      <div class="card-header">
        <i class="fas fa-cogs"></i>
        SQL 運算
      </div>
      <div class="card-body">
        <p class="card-text text-secondary" style="font-size: 1.5rem;">
          點數加總
        </p>
        <i class="fa fa-arrow-down" aria-hidden="true"></i>
      </div>
    </div>
  </div>
</div>

<div class="row">
  <div class="col-md-2 col-sm-4 col-xs-6">
  </div>
  <div class="col-md-2 col-sm-4 col-xs-6">
    <div class="card text-center mb-3" style="min-height: 10rem; max-height: 10rem; vertical-align: middle;">
      <div class="card-header">
        <i class="fas fa-cogs"></i>
        SQL 運算
      </div>
      <div class="card-body">
        <p class="card-text text-secondary" style="font-size: 1.5rem;">
          排除退課名單
        </p>
        <i class="fa fa-arrow-down" aria-hidden="true"></i>
      </div>
    </div>
  </div>
</div>

<div class="row">
  <div class="col-md-2 col-sm-4 col-xs-6">
  </div>
  <div class="col-md-2 col-sm-4 col-xs-6">
    <div class="card text-center mb-3" style="min-height: 10rem; max-height: 10rem; vertical-align: middle;">
      <div class="card-header">
        <i class="fas fa-cogs"></i>
        SQL 運算
      </div>
      <div class="card-body">
        <p class="card-text text-secondary" style="font-size: 1.5rem;">
          點數排名
        </p>
        <i class="fa fa-arrow-down" aria-hidden="true"></i>
      </div>
    </div>
  </div>
</div>


<!-- Storage Modal -->
<div class="modal fade" id="storageModal" tabindex="-1" role="dialog" aria-labelledby="storageModalLabel" aria-hidden="true">
  <div class="modal-dialog modal-lg" role="document">
    <div class="modal-content">
      <div class="modal-header">
        <button type="button" class="close" data-dismiss="modal" aria-label="Close"><span aria-hidden="true">&times;</span></button>
        <h4 class="modal-title" id="storageModalLabel">新增資料源</h4>
      </div>
      <div class="modal-body">
          <div id="storageForm"></div>
      </div>
    </div>
  </div>
</div>

<!-- Step Modal -->
<div class="modal fade" id="stepModal" tabindex="-1" role="dialog" aria-labelledby="stepModalLabel" aria-hidden="true">
  <div class="modal-dialog" role="document">
    <div class="modal-content">
      <div class="modal-header">
        <button type="button" class="close" data-dismiss="modal" aria-label="Close"><span aria-hidden="true">&times;</span></button>
        <h4 class="modal-title" id="storageModalLabel">新增步驟</h4>
      </div>
      <div class="modal-body">
        <div id="stepForm"></div>
      </div>
      <div class="modal-footer">
        <button type="button" class="btn btn-secondary" data-dismiss="modal">Close</button>
        <button type="button" class="btn btn-primary">Save changes</button>
      </div>
    </div>
  </div>
</div>

<script>
    window.StorageFormSchema = @json(App\RuntimeStorage::getAllFormSchema());
</script>
@endsection
