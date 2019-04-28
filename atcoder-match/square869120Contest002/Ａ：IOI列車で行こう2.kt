import java.util.Scanner
 
fun main(args: Array<String>) {
	var sc = Scanner(System.`in`)
 
	val S = sc.next()
	val array = S.toCharArray().map { it == 'I' } // I => true, O => false
	var count = 0
	var current = true
	for (c in array) {
		if (!(current xor c)) {
			count++
			current = !current
		}
	}
	if (current) {
		if (count > 0) {
			count--
		}
	}
	println(count)
}