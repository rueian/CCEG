<?php

/*
|--------------------------------------------------------------------------
| Web Routes
|--------------------------------------------------------------------------
|
| Here is where you can register web routes for your application. These
| routes are loaded by the RouteServiceProvider within a group which
| contains the "web" middleware group. Now create something great!
|
*/

Route::get('/', 'BlueprintController@index');
Route::get('/blueprints', 'BlueprintController@index');
Route::post('/blueprints', 'BlueprintController@store');
Route::put('/blueprints/editable', 'BlueprintController@editable');
Route::get('/blueprints/{id}/edit', 'BlueprintController@edit');
Route::post('/blueprints/{id}/storage', 'BlueprintController@addStorage');
