/*
 * Copyright (c) 1997, 2013, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package java.lang;
import java.lang.ref.*;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Supplier;

/**
 * This class provides thread-local variables.  These variables differ from
 * their normal counterparts in that each thread that accesses one (via its
 * {@code get} or {@code set} method) has its own, independently initialized
 * copy of the variable.  {@code ThreadLocal} instances are typically private
 * static fields in classes that wish to associate state with a thread (e.g.,
 * a user ID or Transaction ID).
 *
 * <p>For example, the class below generates unique identifiers local to each
 * thread.
 * A thread's id is assigned the first time it invokes {@code ThreadId.get()}
 * and remains unchanged on subsequent calls.
 * <pre>
 * import java.util.concurrent.atomic.AtomicInteger;
 *
 * public class ThreadId {
 *     // Atomic integer containing the next thread ID to be assigned
 *     private static final AtomicInteger nextId = new AtomicInteger(0);
 *
 *     // Thread local variable containing each thread's ID
 *     private static final ThreadLocal&lt;Integer&gt; threadId =
 *         new ThreadLocal&lt;Integer&gt;() {
 *             &#64;Override protected Integer initialValue() {
 *                 return nextId.getAndIncrement();
 *         }
 *     };
 *
 *     // Returns the current thread's unique ID, assigning it if necessary
 *     public static int get() {
 *         return threadId.get();
 *     }
 * }
 * </pre>
 * <p>Each thread holds an implicit reference to its copy of a thread-local
 * variable as long as the thread is alive and the {@code ThreadLocal}
 * instance is accessible; after a thread goes away, all of its copies of
 * thread-local instances are subject to garbage collection (unless other
 * references to these copies exist).
 *
 * ThreadLocal看类名就是线程本地变量的意思。从使用上来说，如果定义了一个ThreadLocal，
 * 那么各个线程针对这个ThreadLocal进行get/set都是线程独立的，也就是说，是线程隔离的本地变量。
 * 从实现上来说，每个线程在运行过程中都可以通过Thread.currentThread()获得与之对应的Thread对象，
 * 而每个Thread对象都有一个ThreadLocalMap类型的成员，ThreadLocalMap是一种hashmap，它以ThreadLocal作为key。
 * 所以，通过Thread对象和ThreadLocal对象二者，才可以唯一确定到一个value上去。线程隔离的关键，正是因为这种对应关系用到了Thread对象
 *
 * @author  Josh Bloch and Doug Lea
 * @since   1.2
 */
public class ThreadLocal<T> {
    /**
     * ThreadLocals rely on per-thread linear-probe hash maps attached
     * to each thread (Thread.threadLocals and
     * inheritableThreadLocals).  The ThreadLocal objects act as keys,
     * searched via threadLocalHashCode.  This is a custom hash code
     * (useful only within ThreadLocalMaps) that eliminates collisions
     * in the common case where consecutively constructed ThreadLocals
     * are used by the same threads, while remaining well-behaved in
     * less common cases.
     */
    // threadlocal的hash值
    // 通过内部的AtomicInteger nextHashCode，执行其getAndAdd(HASH_INCREMENT)方法
    // 首次返回0，之后每次递增一个魔术HASH_INCREMENT
    private final int threadLocalHashCode = nextHashCode();

    /**
     * The next hash code to be given out. Updated atomically. Starts at
     * zero.
     */
    private static AtomicInteger nextHashCode =
        new AtomicInteger();

    /**
     * The difference between successively generated hash codes - turns
     * implicit sequential thread-local IDs into near-optimally spread
     * multiplicative hash values for power-of-two-sized tables.
     */
    private static final int HASH_INCREMENT = 0x61c88647;

    /**
     * Returns the next hash code.
     */
    private static int nextHashCode() {
        return nextHashCode.getAndAdd(HASH_INCREMENT);
    }

    /**
     * Returns the current thread's "initial value" for this
     * thread-local variable.  This method will be invoked the first
     * time a thread accesses the variable with the {@link #get}
     * method, unless the thread previously invoked the {@link #set}
     * method, in which case the {@code initialValue} method will not
     * be invoked for the thread.  Normally, this method is invoked at
     * most once per thread, but it may be invoked again in case of
     * subsequent invocations of {@link #remove} followed by {@link #get}.
     *
     * <p>This implementation simply returns {@code null}; if the
     * programmer desires thread-local variables to have an initial
     * value other than {@code null}, {@code ThreadLocal} must be
     * subclassed, and this method overridden.  Typically, an
     * anonymous inner class will be used.
     *
     * @return the initial value for this thread-local
     */
    // 当调用get方法时，对应线程的ThreadLocalMap为null
    // 会调用该方法，默认返回null，可以写个子类重新改方法
    protected T initialValue() {
        return null;
    }

    /**
     * Creates a thread local variable. The initial value of the variable is
     * determined by invoking the {@code get} method on the {@code Supplier}.
     *
     * @param <S> the type of the thread local's value
     * @param supplier the supplier to be used to determine the initial value
     * @return a new thread local variable
     * @throws NullPointerException if the specified supplier is null
     * @since 1.8
     */
    // 这个方法返回的是ThreadLocal的子类SuppliedThreadLocal
    // 该子类内部只重新了initialValue方法，然后initialValue返回值是supplier提供的
    public static <S> ThreadLocal<S> withInitial(Supplier<? extends S> supplier) {
        return new SuppliedThreadLocal<>(supplier);
    }

    /**
     * Creates a thread local variable.
     * @see #withInitial(java.util.function.Supplier)
     */
    public ThreadLocal() {
    }

    /**
     * Returns the value in the current thread's copy of this
     * thread-local variable.  If the variable has no value for the
     * current thread, it is first initialized to the value returned
     * by an invocation of the {@link #initialValue} method.
     *
     * @return the current thread's value of this thread-local
     */
    public T get() {
        // 获取当前线程
        Thread t = Thread.currentThread();
        // 获取线程的属性ThreadLocal.ThreadLocalMap threadLocals
        ThreadLocalMap map = getMap(t);
        // 如果不为null
        if (map != null) {
            ThreadLocalMap.Entry e = map.getEntry(this);
            // entry不为空,返回value
            // 否则继续执行setInitialValue方法
            if (e != null) {
                @SuppressWarnings("unchecked")
                T result = (T)e.value;
                return result;
            }
        }
        // 当前线程的ThreadLocal.ThreadLocalMap threadLocals为null
        return setInitialValue();
    }

    /**
     * Variant of set() to establish initialValue. Used instead
     * of set() in case user has overridden the set() method.
     *
     * @return the initial value
     */
    // 初始化ThreadLocalMap以及初始值
    private T setInitialValue() {
        // 初始化值，默认null
        T value = initialValue();
        // 获取当前线程，以及它的属性ThreadLocal.ThreadLocalMap threadLocals
        Thread t = Thread.currentThread();
        ThreadLocalMap map = getMap(t);
        // 下面就是map不为空则放值
        // map为空则创建一个ThreadLocalMap并防值
        // map中的key就是当前的threadlocal,value才是真正的值
        if (map != null)
            map.set(this, value);
        else
            createMap(t, value);
        return value;
    }

    /**
     * Sets the current thread's copy of this thread-local variable
     * to the specified value.  Most subclasses will have no need to
     * override this method, relying solely on the {@link #initialValue}
     * method to set the values of thread-locals.
     *
     * @param value the value to be stored in the current thread's copy of
     *        this thread-local.
     */
    public void set(T value) {
        // 获取当前线程和对应的ThreadLocalMap
        Thread t = Thread.currentThread();
        ThreadLocalMap map = getMap(t);
        // ThreadLocalMap不为null，直接放值
        if (map != null)
            map.set(this, value);
        // ThreadLocalMap为null，创建一个
        else
            createMap(t, value);
    }

    /**
     * Removes the current thread's value for this thread-local
     * variable.  If this thread-local variable is subsequently
     * {@linkplain #get read} by the current thread, its value will be
     * reinitialized by invoking its {@link #initialValue} method,
     * unless its value is {@linkplain #set set} by the current thread
     * in the interim.  This may result in multiple invocations of the
     * {@code initialValue} method in the current thread.
     *
     * @since 1.5
     */
     public void remove() {
         // 获取当前线程的ThreadLocalMap，然后删掉对应的key
         // 这里只是删掉了key
         ThreadLocalMap m = getMap(Thread.currentThread());
         if (m != null)
             m.remove(this);
     }

    /**
     * Get the map associated with a ThreadLocal. Overridden in
     * InheritableThreadLocal.
     *
     * @param  t the current thread
     * @return the map
     */
    ThreadLocalMap getMap(Thread t) {
        return t.threadLocals;
    }

    /**
     * Create the map associated with a ThreadLocal. Overridden in
     * InheritableThreadLocal.
     *
     * @param t the current thread
     * @param firstValue value for the initial entry of the map
     */
    // 创建一个ThreadLocalMap
    void createMap(Thread t, T firstValue) {
        t.threadLocals = new ThreadLocalMap(this, firstValue);
    }

    /**
     * Factory method to create map of inherited thread locals.
     * Designed to be called only from Thread constructor.
     *
     * @param  parentMap the map associated with parent thread
     * @return a map containing the parent's inheritable bindings
     */
    // 该方法在Thread类的init方法中会被调用
    // 主要是解决了子线程访问父线程ThreadLocal中值的问题
    // 如下代码：
    /**
     * public static ThreadLocal<String> threadLocal = new ThreadLocal<String> ();
     * public static void main (String [] args) {
     * 	threadLocal.set (”123");
     * 	new Thread (() -> {
     * 		System.out.println(”sun:” + threadLocal.get());
     *        }).start() ;
     * 	System.out.println(”main:” + threadLocal.get());
     * }
     * 输入：
     *  main:123
     *  sun:null
     *  修改成如下方式即可解决，参考Thread类的init方法
     * public static ThreadLocal<String> threadLocal = new InheritableThreadLocal<String> ();
     * @param parentMap
     * @return
     */
    static ThreadLocalMap createInheritedMap(ThreadLocalMap parentMap) {
        return new ThreadLocalMap(parentMap);
    }

    /**
     * Method childValue is visibly defined in subclass
     * InheritableThreadLocal, but is internally defined here for the
     * sake of providing createInheritedMap factory method without
     * needing to subclass the map class in InheritableThreadLocal.
     * This technique is preferable to the alternative of embedding
     * instanceof tests in methods.
     */
    T childValue(T parentValue) {
        throw new UnsupportedOperationException();
    }

    /**
     * An extension of ThreadLocal that obtains its initial value from
     * the specified {@code Supplier}.
     */
    static final class SuppliedThreadLocal<T> extends ThreadLocal<T> {

        private final Supplier<? extends T> supplier;

        SuppliedThreadLocal(Supplier<? extends T> supplier) {
            this.supplier = Objects.requireNonNull(supplier);
        }

        @Override
        protected T initialValue() {
            return supplier.get();
        }
    }

    /**
     * ThreadLocalMap is a customized hash map suitable only for
     * maintaining thread local values. No operations are exported
     * outside of the ThreadLocal class. The class is package private to
     * allow declaration of fields in class Thread.  To help deal with
     * very large and long-lived usages, the hash table entries use
     * WeakReferences for keys. However, since reference queues are not
     * used, stale entries are guaranteed to be removed only when
     * the table starts running out of space.
     */
    // 重点
    static class ThreadLocalMap {

        /**
         * The entries in this hash map extend WeakReference, using
         * its main ref field as the key (which is always a
         * ThreadLocal object).  Note that null keys (i.e. entry.get()
         * == null) mean that the key is no longer referenced, so the
         * entry can be expunged from table.  Such entries are referred to
         * as "stale entries" in the code that follows.
         */
        // ThreadLocalMap的value实际存储的是一个Entry对象
        // 并且是一个弱引用的对象
        static class Entry extends WeakReference<ThreadLocal<?>> {
            /** The value associated with this ThreadLocal. */
            Object value;

            Entry(ThreadLocal<?> k, Object v) {
                // 这里最终调用的是父类Reference
                // 并把k赋值给了Reference类中的属性
                super(k);
                value = v;
            }
        }

        /**
         * The initial capacity -- MUST be a power of two.
         */
        // 初始容量16
        private static final int INITIAL_CAPACITY = 16;

        /**
         * The table, resized as necessary.
         * table.length MUST always be a power of two.
         */
        // Entry数组
        private Entry[] table;

        /**
         * The number of entries in the table.
         */
        // entry的个数
        private int size = 0;

        /**
         * The next size value at which to resize.
         */
        // 阈值
        private int threshold; // Default to 0

        /**
         * Set the resize threshold to maintain at worst a 2/3 load factor.
         */
        // 设置阈值
        private void setThreshold(int len) {
            threshold = len * 2 / 3;
        }

        /**
         * Increment i modulo len.
         */
        // 向后计算下一个放入table数组的下标，每次从i的位置递增1，当长度为len时，返回0
        // 这说明table是一个环
        private static int nextIndex(int i, int len) {
            return ((i + 1 < len) ? i + 1 : 0);
        }

        /**
         * Decrement i modulo len.
         */
        // 向前计算，每次递减1，当为0时，长度变为 len - 1
        private static int prevIndex(int i, int len) {
            return ((i - 1 >= 0) ? i - 1 : len - 1);
        }

        /**
         * Construct a new map initially containing (firstKey, firstValue).
         * ThreadLocalMaps are constructed lazily, so we only create
         * one when we have at least one entry to put in it.
         */
        // 构造方法
        ThreadLocalMap(ThreadLocal<?> firstKey, Object firstValue) {
            // 初始容量
            table = new Entry[INITIAL_CAPACITY];
            // 获取ThreadLocal的hash值然后对数组取模，获取对应的下标
            int i = firstKey.threadLocalHashCode & (INITIAL_CAPACITY - 1);
            // 因为是刚初始化的，所以这里直接指定就可以
            table[i] = new Entry(firstKey, firstValue);
            size = 1;
            // 设置阈值
            setThreshold(INITIAL_CAPACITY);
        }

        /**
         * Construct a new map including all Inheritable ThreadLocals
         * from given parent map. Called only by createInheritedMap.
         *
         * @param parentMap the map associated with parent thread.
         */
        // 将parentMap中保存的记录添加到当前类的table数组中
        private ThreadLocalMap(ThreadLocalMap parentMap) {
            Entry[] parentTable = parentMap.table;
            int len = parentTable.length;
            setThreshold(len);
            table = new Entry[len];

            for (int j = 0; j < len; j++) {
                Entry e = parentTable[j];
                if (e != null) {
                    @SuppressWarnings("unchecked")
                    ThreadLocal<Object> key = (ThreadLocal<Object>) e.get();
                    if (key != null) {
                        Object value = key.childValue(e.value);
                        Entry c = new Entry(key, value);
                        int h = key.threadLocalHashCode & (len - 1);
                        while (table[h] != null)
                            h = nextIndex(h, len);
                        table[h] = c;
                        size++;
                    }
                }
            }
        }

        /**
         * Get the entry associated with key.  This method
         * itself handles only the fast path: a direct hit of existing
         * key. It otherwise relays to getEntryAfterMiss.  This is
         * designed to maximize performance for direct hits, in part
         * by making this method readily inlinable.
         *
         * @param  key the thread local object
         * @return the entry associated with key, or null if no such
         */
        // 获取值
        private Entry getEntry(ThreadLocal<?> key) {
            // 通过ThreadLocal的hash值获取在table的下标
            int i = key.threadLocalHashCode & (table.length - 1);
            Entry e = table[i];
            // 如果该位置不为null 并且对应的ThreadLocal就是当前的ThreadLocal
            // 那么直接返回该值
            if (e != null && e.get() == key)
                return e;
            // 如果为null，那么可能是发生了hash冲突
            // 1.当前ThreadLocal是有对应值的，但是由于hash冲突，在tabel数组的下标并不是i
            // 2.当前ThreadLocal就是没有对应值
            else
                return getEntryAfterMiss(key, i, e);
        }

        /**
         * Version of getEntry method for use when key is not found in
         * its direct hash slot.
         *
         * @param  key the thread local object
         * @param  i the table index for key's hash code
         * @param  e the entry at table[i]
         * @return the entry associated with key, or null if no such
         */
        // 从i位置开始，获取key对应的value
        private Entry getEntryAfterMiss(ThreadLocal<?> key, int i, Entry e) {
            Entry[] tab = table;
            int len = tab.length;
            // 循环
            while (e != null) {
                ThreadLocal<?> k = e.get();
                // 每次循环后，获取对应位置i的entry的ThreadLocal，如果和参数key相等则直接返回对应Entry
                if (k == key)
                    return e;
                // 如果k为null，
                if (k == null)
                    // 清空该位置
                    // 执行完该方法后，tabel数组中的entry很可能有的发生了位置变化
                    expungeStaleEntry(i);
                // 如果k不为null
                else
                    // 获取下一个下标
                    i = nextIndex(i, len);
                // 获取下标i对应的entry
                e = tab[i];
            }
            return null;
        }

        /**
         * Set the value associated with key.
         *
         * @param key the thread local object
         * @param value the value to be set
         */
        // 设置值
        private void set(ThreadLocal<?> key, Object value) {

            // We don't use a fast path as with get() because it is at
            // least as common to use set() to create new entries as
            // it is to replace existing ones, in which case, a fast
            // path would fail more often than not.

            Entry[] tab = table;
            int len = tab.length;
            // 获取key对应的数组下标
            int i = key.threadLocalHashCode & (len-1);
            // 从i的下一个位置开始遍历获取对应的entry，如果该位置entry不为null，判断执行两个操作
            for (Entry e = tab[i];
                 e != null;
                 e = tab[i = nextIndex(i, len)]) {
                ThreadLocal<?> k = e.get();
                // 如果位置的ThreadLocal和参数传进来的ThreadLocal一致，替换掉旧值
                if (k == key) {
                    e.value = value;
                    return;
                }
                // 如果该位置为对应的ThreadLocal为null，那么需要清理一下
                // 并把参数key、value保存到tabel中去
                if (k == null) {
                    replaceStaleEntry(key, value, i);
                    return;
                }
            }
            /* 执行到这里说明上面for循环中i位置对于的entry e为null了还没有找到对应的ThreadLocal */

            // 创建一个新的entry,赋值到i位置
            tab[i] = new Entry(key, value);
            int sz = ++size;
            // 如果没有清理掉任何的stale entry并且当前数组容量达到了阈值
            // 那么扩容
            if (!cleanSomeSlots(i, sz) && sz >= threshold)
                rehash();
        }

        /**
         * Remove the entry for key.
         */
        // 删除指定的key
        private void remove(ThreadLocal<?> key) {
            Entry[] tab = table;
            int len = tab.length;
            // 计算key的下标
            int i = key.threadLocalHashCode & (len-1);
            // 从下标位置开始往后查找
            for (Entry e = tab[i];
                 e != null;
                 e = tab[i = nextIndex(i, len)]) {
                // 找到了对应的key
                if (e.get() == key) {
                    // 清空引用
                    e.clear();
                    // 删除stale entry
                    expungeStaleEntry(i);
                    return;
                }
            }
        }

        /**
         * Replace a stale entry encountered during a set operation
         * with an entry for the specified key.  The value passed in
         * the value parameter is stored in the entry, whether or not
         * an entry already exists for the specified key.
         *
         * As a side effect, this method expunges all stale entries in the
         * "run" containing the stale entry.  (A run is a sequence of entries
         * between two null slots.)
         *
         * @param  key the key
         * @param  value the value to be associated with key
         * @param  staleSlot index of the first stale entry encountered while
         *         searching for key.
         */
        private void replaceStaleEntry(ThreadLocal<?> key, Object value,
                                       int staleSlot) {
            Entry[] tab = table;
            int len = tab.length;
            Entry e;

            // Back up to check for prior stale entry in current run.
            // We clean out whole runs at a time to avoid continual
            // incremental rehashing due to garbage collector freeing
            // up refs in bunches (i.e., whenever the collector runs).
            // 标记要擦除的起始位置
            int slotToExpunge = staleSlot;
            // 从staleSlot的前一个位置开始向前查找，直到找到位置i，该位置entry为null，此时slotToExpunge = 当前i + 1
            // 也就是从staleSlot的前一个位置开始，一直到i+1的位置，所有位置的entry都不为null，称为staleSlot的前段
            // 此时slotToExpunge记录的是前段中最后一个stale entry，如果没有slotToExpunge还是staleSlot
            for (int i = prevIndex(staleSlot, len); (e = tab[i]) != null; i = prevIndex(i, len))
                if (e.get() == null)
                    slotToExpunge = i;

            // Find either the key or trailing null slot of run, whichever
            // occurs first
            // 从staleSlot的后一个位置开始向后查找，直到找到位置i，该位置entry为null，然后退出循环
            // 也就是从staleSlot的后一个位置开始，一直到i-1的位置，所有位置的entry都不为null，称为staleSlot的后段
            for (int i = nextIndex(staleSlot, len);
                 (e = tab[i]) != null;
                 i = nextIndex(i, len)) {
                ThreadLocal<?> k = e.get();

                // If we find key, then we need to swap it
                // with the stale entry to maintain hash table order.
                // The newly stale slot, or any other stale slot
                // encountered above it, can then be sent to expungeStaleEntry
                // to remove or rehash all of the other entries in run.

                // 在找staleSlot的后段中找到了对应的ThreadLocal，位置为下标i
                if (k == key) {
                    // 更新旧值
                    e.value = value;
                    // 交换位置i和staleSlot的entry
                    // 位置i为由于之前放入冲突，导致往后移动后的下标，此时需要将该值往前方，交换位置即可(这里思考staleSlot的含义得出此结论)
                    tab[i] = tab[staleSlot];
                    tab[staleSlot] = e;

                    // Start expunge at preceding stale entry if it exists
                    // 1.如果slotToExpunge == staleSlot，说明staleSlot的前段没有stale entry
                    //   此时更新一下slotToExpunge = i是因为上面的交换操作后，i位置变为了stale entry
                    // 2.如果slotToExpunge != staleSlot，说明staleSlot的前段有stale entry
                    //   此时就不需要更新slotToExpunge，因为后续清理操作是从slotToExpunge往后查找
                    if (slotToExpunge == staleSlot)
                        slotToExpunge = i;
                    // 清理操作
                    cleanSomeSlots(expungeStaleEntry(slotToExpunge), len);
                    return;
                }

                // If we didn't find stale entry on backward scan, the
                // first stale entry seen while scanning for key is the
                // first still present in the run.
                // 如果i位置对于的ThreadLocal为null，并且staleSlot的前段没有stale entry
                // 那么此时更新slotToExpunge = i，后续如果再有k为null的entry，slotToExpunge就不会更新了
                // 所以综上所述lotToExpunge要么记录staleSlot前段中最终的一个stale entry，要么记录后的中最早的一个stale entry
                if (k == null && slotToExpunge == staleSlot)
                    slotToExpunge = i;
            }

            /* 执行到这里说明没有找到对应entry的k == 传入的参数key */

            // If key not found, put new entry in stale slot
            // 此时将新的key 和value封装为entry放到staleSlot即可
            tab[staleSlot].value = null;
            tab[staleSlot] = new Entry(key, value);

            // If there are any other stale entries in run, expunge them
            // slotToExpunge != staleSlot说明staleSlot的前段没有stale entry，但是后段有，执行清理操作
            if (slotToExpunge != staleSlot)
                cleanSomeSlots(expungeStaleEntry(slotToExpunge), len);
        }

        /**
         * Expunge a stale entry by rehashing any possibly colliding entries
         * lying between staleSlot and the next null slot.  This also expunges
         * any other stale entries encountered before the trailing null.  See
         * Knuth, Section 6.4
         *
         * @param staleSlot index of slot known to have null key
         * @return the index of the next null slot after staleSlot
         * (all between staleSlot and this slot will have been checked
         * for expunging).
         */
        // 清理stale entry
        private int expungeStaleEntry(int staleSlot) {
            Entry[] tab = table;
            int len = tab.length;

            // expunge entry at staleSlot
            // 删除对应下标位置entry的value
            // 然后将对应下标位置空
            tab[staleSlot].value = null;
            tab[staleSlot] = null;
            size--;

            // Rehash until we encounter null
            Entry e;
            int i;
            // 遍历table，从staleSlot下一个位置开始
            // i 记录staleSlot下一个位置
            // e 记录i位置的entry
            // i 每次递增，够len后变为0
            for (i = nextIndex(staleSlot, len);
                 (e = tab[i]) != null;
                 i = nextIndex(i, len)) {
                ThreadLocal<?> k = e.get();
                // 如果i位置的key为null，继续清空该位置
                if (k == null) {
                    e.value = null;
                    tab[i] = null;
                    size--;
                // 如果i位置的key不为null
                } else {
                    // 重新获取i位置的ThreadLocal的下标
                    int h = k.threadLocalHashCode & (len - 1);
                    // 如果重新计算后的下标和当前的下标不一致
                    // 那么需要移动i位置的entry并清空该位置
                    if (h != i) {
                        tab[i] = null;

                        // Unlike Knuth 6.4 Algorithm R, we must scan until
                        // null because multiple entries could have been stale.
                        // 如果重新计算的位置不为null，那么判断下一个位置
                        // 直到找到一个为null的位置，将当前entry赋值过去
                        while (tab[h] != null)
                            h = nextIndex(h, len);
                        tab[h] = e;
                    }
                }
            }
            // 返回旧的下标
            return i;
        }

        /**
         * Heuristically scan some cells looking for stale entries.
         * This is invoked when either a new element is added, or
         * another stale one has been expunged. It performs a
         * logarithmic number of scans, as a balance between no
         * scanning (fast but retains garbage) and a number of scans
         * proportional to number of elements, that would find all
         * garbage but would cause some insertions to take O(n) time.
         *
         * @param i a position known NOT to hold a stale entry. The
         * scan starts at the element after i.
         *
         * @param n scan control: {@code log2(n)} cells are scanned,
         * unless a stale entry is found, in which case
         * {@code log2(table.length)-1} additional cells are scanned.
         * When called from insertions, this parameter is the number
         * of elements, but when from replaceStaleEntry, it is the
         * table length. (Note: all this could be changed to be either
         * more or less aggressive by weighting n instead of just
         * using straight log n. But this version is simple, fast, and
         * seems to work well.)
         *
         * @return true if any stale entries have been removed.
         */
        private boolean cleanSomeSlots(int i, int n) {
            boolean removed = false;
            Entry[] tab = table;
            int len = tab.length;
            do {
                // 从i的下一个位置开始遍历
                // 为什么从i的下一个位置开始，移步调用方（因为i保存了新的值）
                i = nextIndex(i, len);
                Entry e = tab[i];
                if (e != null && e.get() == null) {
                    n = len;
                    removed = true;
                    // 清理stale entry
                    i = expungeStaleEntry(i);
                }
            } while ( (n >>>= 1) != 0);// n = n / 2
            return removed;
        }

        /**
         * Re-pack and/or re-size the table. First scan the entire
         * table removing stale entries. If this doesn't sufficiently
         * shrink the size of the table, double the table size.
         */
        private void rehash() {
            expungeStaleEntries();

            // Use lower threshold for doubling to avoid hysteresis
            if (size >= threshold - threshold / 4)
                resize();
        }

        /**
         * Double the capacity of the table.
         */
        // 扩容，将旧tabel里的entry，转移到新table
        private void resize() {
            Entry[] oldTab = table;
            int oldLen = oldTab.length;
            int newLen = oldLen * 2;
            Entry[] newTab = new Entry[newLen];
            int count = 0;

            for (int j = 0; j < oldLen; ++j) {
                Entry e = oldTab[j];
                if (e != null) {
                    ThreadLocal<?> k = e.get();
                    if (k == null) {
                        e.value = null; // Help the GC
                    } else {
                        int h = k.threadLocalHashCode & (newLen - 1);
                        while (newTab[h] != null)
                            h = nextIndex(h, newLen);
                        newTab[h] = e;
                        count++;
                    }
                }
            }

            setThreshold(newLen);
            size = count;
            table = newTab;
        }

        /**
         * Expunge all stale entries in the table.
         */
        // 遍历table表，删除里面所有的stale entry
        private void expungeStaleEntries() {
            Entry[] tab = table;
            int len = tab.length;
            for (int j = 0; j < len; j++) {
                Entry e = tab[j];
                if (e != null && e.get() == null)
                    expungeStaleEntry(j);
            }
        }
    }
}
