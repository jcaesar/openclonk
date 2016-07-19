#!/usr/bin/env bash

set -e -u -x

for fn in *.h; do
	f="${fn/.h/}"
	rm -rf "$f"
	mkdir "$f"
	../../../c4script "$fn" 2>&1 | grep -Pzo "(?<=\.\.\.\n)(.|\n)*(metadata|attributes #).*\n" | tee "${fn/.h/.ll}" | ( cd "$f"; ${OPT:-opt} -analyze -dot-cfg )
	( cd "$f";
	for d in *.dot; do
		dot <"$d" -Tpng >"$d"_"${fn/h/png}"
	done
	)
done
