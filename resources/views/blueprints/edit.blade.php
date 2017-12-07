@extends('main')

@section('jumbotron')
<div class="jumbotron jumbotron-fluid">
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
  
</div>

@endsection
