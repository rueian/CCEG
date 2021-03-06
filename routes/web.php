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
Route::delete('/blueprints/{id}/storage/{key}', 'BlueprintController@removeStorage');
Route::post('/blueprints/{id}/step', 'BlueprintController@addStep');
Route::put('/blueprints/{id}/step/{key}', 'BlueprintController@editStep');
Route::delete('/blueprints/{id}/step/{key}', 'BlueprintController@removeStep');
Route::post('/blueprints/{id}/runtimes', 'BlueprintController@createRuntime');
Route::get('/blueprints/{id}/runtimes', 'BlueprintController@listRuntime');
Route::delete('/blueprints/{id}/runtimes', 'BlueprintController@deleteRuntime');
Route::delete('/blueprints/{id}', 'BlueprintController@delete');

Route::post('/runtimes/{id}/one-step',  'RuntimeController@runOneStep');
Route::post('/runtimes/{id}/run-all', 'RuntimeController@runToDone');
Route::post('/runtimes/{id}/reset', 'RuntimeController@resetSteps');
Route::post('/runtimes/{id}/import/{fromId}', 'RuntimeController@importInputStorages');

Route::post('/storages/{id}/import', 'RuntimeStorageController@import');
Route::get('/storages/{id}/export', 'RuntimeStorageController@export');

Route::post('/runtimes/{id}/storages/{key}/import', 'RuntimeStorageController@importWithRuntime');
Route::get('/runtimes/{id}/storages/{key}/export', 'RuntimeStorageController@exportWithRuntime');