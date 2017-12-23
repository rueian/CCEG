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

    <div class="container-fluid h-100">
      @yield('container')
    </div>

    @yield('beforeScript')
    <script src="{{ mix('js/app.js') }}"></script>
    @yield('afterScript')
  </body>
</html>