<?php

namespace App\Console\Commands;

use Illuminate\Console\Command;
use DB;

class WaitDbConnection extends Command
{
    /**
     * The name and signature of the console command.
     *
     * @var string
     */
    protected $signature = 'wait:db-connection {times=60}';

    /**
     * The console command description.
     *
     * @var string
     */
    protected $description = 'Test db connection every second for maximum {times|60}, or until db is ready.';

    /**
     * Create a new command instance.
     *
     * @return void
     */
    public function __construct()
    {
        parent::__construct();
    }

    /**
     * Execute the console command.
     *
     * @return mixed
     */
    public function handle()
    {
        $counter = 0;
        $times = intval($this->argument('times'));

        while($counter++ < $times) {
            try {
                $this->info('Trying to connect db ...');
                DB::select('select 1');
            } catch (\Illuminate\Database\QueryException $e) {
                sleep(1);
                continue;
            }

            $this->info('Success to connect db.');
            return;
        }

        $this->error('Fail to connect db, Maximum retry times exceeded.');
    }
}
