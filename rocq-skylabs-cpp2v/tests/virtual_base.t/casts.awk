# Print each Cunsupported, Cderived2base and Cbase2derived cast of a
# `cpp2v --no-sharing` file under the declaration it occurs in.
/^    \(D/ { decl = $0; sub(/^ */, "", decl); shown = 0 }
{
    line = $0
    while (match(line, /\(C(unsupported|derived2base|base2derived) /)) {
        line = substr(line, RSTART)
        depth = 0
        for (i = 1; i <= length(line); i++) {
            c = substr(line, i, 1)
            if (c == "(") depth++
            else if (c == ")" && --depth == 0) break
        }
        if (!shown) { print decl; shown = 1 }
        print "  " substr(line, 1, i)
        line = substr(line, i + 1)
    }
}
