#!/bin/sh
# record scan for E874: entries E801+ of the running log mentioning a search-size or node-count profile of the V3 / chain-cover search
cd "/Users/trentpalelei/Desktop/Math Ex"
awk '/^## E[0-9]+/{h=$2} /v3_exact_chain|V3.*nodes|nodes.*V3|chain_cover_v4.*nodes|by depth|bydepth|growth profile/{print h": "substr($0,1,90)}' docs/n8/RUNNING_LOG_order8_v1.md | sort -u
