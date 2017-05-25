#!/bin/bash
sudo /etc/init.d/postgresql start

exec "$@"
