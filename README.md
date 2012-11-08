mydotvim
========

my dot vim folder

;; Get my dotvim
    git clone https://kinghom@github.com/kinghom/mydotvim.git
    git submodule init
    git submodule update

;; Add a submodule
    git submodule add URL bundle/NAME
    git add .
    git ci -m "some comment"
    git push

;; Update submodule
    git submodule foreach git pull origin master
