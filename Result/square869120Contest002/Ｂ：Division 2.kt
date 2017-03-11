import java.util.Scanner

import kotlin.properties.Delegates

fun main(args: Array<String>) {
	var sc = Scanner(System.`in`)

	val n = sc.nextLong()
	val q = sc.nextInt()
	val a = Array(q, { sc.nextInt() })

	val tree = Tree(a)
	tree.parse()
}

class Tree(private val array: Array<Int>) {
	private val field = Array(2 shl array.size - 1, { 1 })

	fun parse() {
		for (i in 0..array.size - 1) {

			val block = field.size / (2 shl i)
			for (j in 0..i) {
				for (k in (j * block * 2)..(j * block * 2 + block - 1)) {
					field[k] *= array[i]
				}
			}
		}
	}
}