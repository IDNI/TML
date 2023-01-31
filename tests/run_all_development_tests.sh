for dir in `find ./development -mindepth 1 -maxdepth 1 -type d -not -name "expected"`; do
        ./run_regression_tests.sh $dir $@
done
