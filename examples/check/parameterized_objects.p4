control C() {
    apply { }
}

control Cctrl();

control D()(Cctrl c1, Cctrl c2){
    apply{
        c1.apply();
        c2.apply();
    }
}

control E(){
	C() c1;
	C() c2;
	D(c1, c2) d;
    apply {
    	  d.apply();
    }
}

control Ectrl();
package top(Ectrl _e);
top(E()) main;
