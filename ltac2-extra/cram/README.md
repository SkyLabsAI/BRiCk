Automation Cram Tests
===========================

We check in infrastructure for building cram tests to make them easier to
develop on.

Creating a New Cram Test
-------------------------------

To create a new cram test, simply create a directory with a suffix `.t` and run:

```shell
mkdir test_name.t
./setup-tests.sh
git add -a test_name.t
```

You can then add files to do directory and check them in. Don't forget to run

```shell
dune runtest test_name.t --auto-promote
```
