<!doctype html>
<html lang="zh-tw">
  <head>
    <title>CCEG</title>
    <!-- Required meta tags -->
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1, shrink-to-fit=no">
    <meta name="csrf-token" content="{{ csrf_token() }}">

    <script defer src="https://use.fontawesome.com/releases/v5.0.0/js/all.js"></script>

    <link rel="stylesheet" href="{{ mix('css/app.css') }}">
  </head>
  <body>
    
    @include('navbar')

    @yield('jumbotron')

    <div class="container-fluid">
      @yield('container')
    </div>

    <script src="{{ mix('js/app.js') }}"></script>
  </body>
</html>