#!/usr/bin/env bash

docker run \
	--volume="$(pwd):/code" \
	--workdir=/code \
	scottfleischman/agda:2.5.4.2 \
	${@:1}
