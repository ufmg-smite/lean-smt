#!/usr/bin/env bash
# check_one.sh with the coarse (monolithic ARITH_COVERINGS_UNIV) reconstruction; a separate
# executable so that no extra argument has to be forwarded by submit-job.
exec "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/check_one.sh" --coarse "$@"
