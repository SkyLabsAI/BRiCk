  $ cat > good.v <<'EOF'
  > Elpi Accumulate lp:{{
  > #line 3 "good.v"
  > 
  >   pred ok.
  > }}.
  > EOF
  $ rocq-elpi-lint good.v
  Elpi Accumulate lp:{{
  #line 3 "good.v"
  
    pred ok.
  }}.

  $ cat > whitespace.v <<'EOF'
  > #[phase="both"] Elpi Accumulate lp:{{   #line    2	"whitespace.v"
  > 
  >   pred ok.
  > }}.
  > EOF
  $ rocq-elpi-lint whitespace.v
  #[phase="both"] Elpi Accumulate lp:{{#line 2 "whitespace.v"
  
    pred ok.
  }}.

  $ cat > missing.v <<'EOF'
  > Elpi Accumulate lp:{{
  > 
  >   pred missing.
  > }}.
  > EOF
  $ rocq-elpi-lint missing.v
  Elpi Accumulate lp:{{
  
  #line 4 "missing.v"
    pred missing.
  }}.

  $ cat > stale.v <<'EOF'
  > Elpi Accumulate lp:{{
  > #line 10 "stale.v"
  > 
  >   pred stale.
  > }}.
  > EOF
  $ rocq-elpi-lint stale.v
  Elpi Accumulate lp:{{
  #line 3 "stale.v"
  
    pred stale.
  }}.

  $ cat > wrong-file.v <<'EOF'
  > Elpi Accumulate lp:{{
  > #line 3 "other.v"
  > 
  >   pred wrong_file.
  > }}.
  > EOF
  $ rocq-elpi-lint wrong-file.v
  Elpi Accumulate lp:{{
  #line 3 "wrong-file.v"
  
    pred wrong_file.
  }}.

  $ cat > before-first-line-added.v <<'EOF'
  > Elpi Accumulate lp:{{
  >   pred missing_directive.
  > }}.
  > 
  > Elpi Accumulate lp:{{
  > #line 7 "before-first-line-added.v"
  > 
  >   pred second_still_current.
  > }}.
  > EOF
  $ rocq-elpi-lint before-first-line-added.v
  Elpi Accumulate lp:{{
  #line 3 "before-first-line-added.v"
    pred missing_directive.
  }}.
  
  Elpi Accumulate lp:{{
  #line 8 "before-first-line-added.v"
  
    pred second_still_current.
  }}.

  $ cat > after-first-line-added.v <<'EOF'
  > Elpi Accumulate lp:{{
  > #line 3 "after-first-line-added.v"
  >   pred first_fixed.
  > }}.
  > 
  > Elpi Accumulate lp:{{
  > #line 7 "after-first-line-added.v"
  > 
  >   pred second_now_stale.
  > }}.
  > EOF
  $ rocq-elpi-lint after-first-line-added.v
  Elpi Accumulate lp:{{
  #line 3 "after-first-line-added.v"
    pred first_fixed.
  }}.
  
  Elpi Accumulate lp:{{
  #line 8 "after-first-line-added.v"
  
    pred second_now_stale.
  }}.

  $ cat > a.v <<'EOF'
  > Elpi Accumulate lp:{{
  >   pred a.
  > }}.
  > EOF
  $ cat > b.v <<'EOF'
  > Elpi Accumulate lp:{{
  > #line 9 "other.v"
  >   pred b.
  > }}.
  > EOF
  $ cat > notes.txt <<'EOF'
  > Elpi Accumulate lp:{{
  >   this is not a Rocq file.
  > }}.
  > EOF
  $ rocq-elpi-lint -i a.v notes.txt b.v
  $ find . -maxdepth 1 -name '.rocq-elpi-lint-*' -print
  $ cat a.v
  Elpi Accumulate lp:{{
  #line 3 "a.v"
    pred a.
  }}.
  $ cat b.v
  Elpi Accumulate lp:{{
  #line 3 "b.v"
    pred b.
  }}.
  $ cat notes.txt
  Elpi Accumulate lp:{{
    this is not a Rocq file.
  }}.

  $ rocq-elpi-lint a.v b.v
  rocq-elpi-lint: without -i, pass exactly one file
  [2]

  $ rocq-elpi-lint notes.txt
