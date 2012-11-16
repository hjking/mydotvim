mydotvim
========

## my dot vim folder

1. Get my dotvim
```shell
    git clone https://kinghom@github.com/kinghom/mydotvim.git
    git submodule init
    git submodule update
```

2. Add a submodule
```shell
    git submodule add URL bundle/NAME
    git add .
    git ci -m "some comment"
    git push
```

3. Update submodule
```shell
    git submodule foreach git pull origin master
```
