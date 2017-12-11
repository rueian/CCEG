<?php

use Illuminate\Support\Facades\Schema;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Database\Migrations\Migration;

class InitTables extends Migration
{
    /**
     * Run the migrations.
     *
     * @return void
     */
    public function up()
    {
        Schema::create('blueprints', function($table) {
            $table->increments('id');
            $table->string('name');
            $table->text('note')->nullable();
            $table->json('payload')->nullable();
            $table->timestamps();
        });

        Schema::create('runtimes', function($table) {
            $table->increments('id');
            $table->unsignedInteger('blueprint_id')->index();
            $table->string('state');
            $table->json('error')->nullable();
            $table->timestamps();

            $table->foreign('blueprint_id')->references('id')->on('blueprints')->onDelete('cascade');
        });

        Schema::create('runtime_storages', function($table) {
            $table->increments('id');
            $table->unsignedInteger('runtime_id');
            $table->string('key');
            $table->string('name')->nullable();
            $table->string('type');
            $table->json('payload')->nullable();
            $table->string('state');
            $table->json('error')->nullable();
            $table->timestamps();

            $table->unique(['runtime_id', 'key']);

            $table->foreign('runtime_id')->references('id')->on('runtimes')->onDelete('cascade');
        });

        Schema::create('steps', function($table) {
            $table->increments('id');
            $table->unsignedInteger('runtime_id')->index();
            $table->string('key');
            $table->string('name')->nullable();
            $table->text('note')->nullable();
            $table->string('type');
            $table->json('param')->nullable();
            $table->string('state');
            $table->json('error')->nullable();
            $table->timestamps();

            $table->unique(['runtime_id', 'key']);

            $table->foreign('runtime_id')->references('id')->on('runtimes')->onDelete('cascade');
        });

        Schema::create('step_connections', function($table) {
            $table->increments('id');
            $table->unsignedInteger('runtime_id')->index();
            $table->unsignedInteger('step_id');
            $table->unsignedInteger('runtime_storage_id');
            $table->string('type');
            $table->timestamps();

            $table->unique(['step_id', 'runtime_storage_id']);

            $table->foreign('runtime_id')->references('id')->on('runtimes')->onDelete('cascade');
            $table->foreign('step_id')->references('id')->on('steps')->onDelete('cascade');
            $table->foreign('runtime_storage_id')->references('id')->on('runtime_storages')->onDelete('cascade');
        });
    }

    /**
     * Reverse the migrations.
     *
     * @return void
     */
    public function down()
    {
        Schema::dropIfExists('step_connections');
        Schema::dropIfExists('steps');
        Schema::dropIfExists('runtime_storages');
        Schema::dropIfExists('runtimes');
        Schema::dropIfExists('blueprints');
    }
}
