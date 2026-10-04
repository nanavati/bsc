#! /usr/bin/env bash
set -euo pipefail

export TMOUT=1

OUTPUT_DIR=${1:-.}
mkdir -p "$OUTPUT_DIR"

# -------------------------
# GIT

# Arguments: 1=commit hash, 2=describe string
genGITBuildVersion () {
    echo "module BuildVersion(buildVersion, buildVersionNum, buildVersionName) where" > "$OUTPUT_DIR/BuildVersion.hs.new";

    echo "import Warmup ()" >> "$OUTPUT_DIR/BuildVersion.hs.new";
    echo >> "$OUTPUT_DIR/BuildVersion.hs.new";
    echo buildVersion :: String >> "$OUTPUT_DIR/BuildVersion.hs.new";
    echo buildVersion = \"$1\" >> "$OUTPUT_DIR/BuildVersion.hs.new";

    echo >> "$OUTPUT_DIR/BuildVersion.hs.new";
    echo buildVersionNum :: Integer >> "$OUTPUT_DIR/BuildVersion.hs.new";
    echo buildVersionNum = 0x$1 >> "$OUTPUT_DIR/BuildVersion.hs.new";

    echo >> "$OUTPUT_DIR/BuildVersion.hs.new";
    echo buildVersionName :: String >> "$OUTPUT_DIR/BuildVersion.hs.new";
    echo buildVersionName = \"$2\" >> "$OUTPUT_DIR/BuildVersion.hs.new";

    if test -f "$OUTPUT_DIR/BuildVersion.hs"; then
	if !(diff "$OUTPUT_DIR/BuildVersion.hs" "$OUTPUT_DIR/BuildVersion.hs.new"); then
            mv "$OUTPUT_DIR/BuildVersion.hs.new" "$OUTPUT_DIR/BuildVersion.hs";
	else
            echo "BuildVersion.hs up-to-date";
            rm "$OUTPUT_DIR/BuildVersion.hs.new";
	fi;
    else
	mv "$OUTPUT_DIR/BuildVersion.hs.new" "$OUTPUT_DIR/BuildVersion.hs";
    fi;
}

# -------------------------

if ( test -f "$OUTPUT_DIR/BuildVersion.hs" ) && [ "$NOUPDATEBUILDVERSION" = 1 ] ; then
    echo "BuildVersion.hs not modified"
else

    if [ "$NOGIT" = 1 ] ; then
	GITCOMMIT="0000000"
	GITDESCR="no-git"
    else

	# If the source was exported (via 'git archive')
	if [[ '$Format:%%$' == "%" ]]; then
	    GITCOMMIT='$Format:%h$'
	    if [[ '$Format:%D$' =~ tag:\ ([^ ]+) ]]; then
		GITDESCR="${BASH_REMATCH[1]}"
	    else
		GITDESCR="archive-g${GITCOMMIT}"
	    fi
	else

	    # Get the current commit hash
	    GITCOMMIT=`git show -s --format=%h HEAD`
	    if ! GITDESCR=`git describe --tags`; then
		GITDESCR="untagged-g${GITCOMMIT}"
	    fi

	fi
    fi
    genGITBuildVersion ${GITCOMMIT} ${GITDESCR}

fi

# -------------------------
