package test.concurrent.locks;

import java.util.concurrent.locks.LockSupport;

public class LockSupportDemo {

    public static void main(String[] args) {

        try {
            Thread t1 = new Thread(()  -> {
                System.out.println("t1 start park");
                LockSupport.park();
                System.out.println("t1 start park done");
            });

            Thread t2 = new Thread(()  -> {
                System.out.println("t2 unpark t1");
                LockSupport.unpark(t1);
                System.out.println("t2 unpark t1 done");
            });

            t1.start();
            Thread.sleep(1000);
            t2.start();
        }catch (Exception e){
            e.printStackTrace();
        }

    }
}
