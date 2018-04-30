#!/bin/sh

docker-compose up -d mysql
docker-compose up -d cceg

docker-compose exec cceg php artisan wait:db-connection
docker-compose exec cceg php artisan migrate
docker-compose exec cceg php artisan db:seed