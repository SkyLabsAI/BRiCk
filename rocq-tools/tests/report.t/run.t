  $ cat build.log | rocq-perf.code-quality-report 2> /dev/null
  [
    {
      "description": "Unused variable: f.",
      "check_name": "warning:ltac2-unused-variable",
      "fingerprint": "1a37d999b358dc8a06d198887bcde86d",
      "severity": "minor",
      "location": {
        "path": "dir/file.v",
        "positions": {
          "begin": { "line": 42, "column": 6 },
          "end": { "line": 42, "column": 7 }
        }
      }
    },
    {
      "description": "Non-empty stdout when building using \"rocq compile\".",
      "check_name": "warning:non-empty-stdout",
      "fingerprint": "72356f3fed2061b8aa32ffec58530eea",
      "severity": "minor",
      "location": {
        "path": "dir1/dir2/tests.v",
        "positions": {
          "begin": { "line": 0, "column": -1 },
          "end": { "line": 0, "column": -1 }
        }
      }
    },
    {
      "description": "This is a very\nlong warning on several lines.",
      "check_name": "warning:long-warning",
      "fingerprint": "6dcd18b96ff1cb143b1ac7102c39a804",
      "severity": "minor",
      "location": {
        "path": "dir/other_file.v",
        "positions": {
          "begin": { "line": 28, "column": 4 },
          "end": { "line": 28, "column": 17 }
        }
      }
    },
    {
      "description": "Some warning.",
      "check_name": "warning:some-warning",
      "fingerprint": "12c09b22f93cec3c59d73b41748eb317",
      "severity": "minor",
      "location": {
        "path": "dir/nested_dir/file.v",
        "positions": {
          "begin": { "line": 54, "column": 4 },
          "end": { "line": 54, "column": 17 }
        }
      }
    }
  ]
  $ cat build.log | rocq-perf.code-quality-report 1> /dev/null
  Warning: dangling input line.
      3 | This is junk, and an empty line next.
  Warning: dangling input line.
      4 | 
  Warning: dangling input line.
      5 | This is more junk.
  Warning: dangling input line.
     14 | Junk line terminated with a closing bracket ]
  Warning: dangling input line.
     17 | Junk at the end with an opening bracket. [
