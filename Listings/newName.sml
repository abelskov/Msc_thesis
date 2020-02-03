val counter = ref 1

fun newName name = 
  let 
    val n = !counter
    val () = counter := !counter + 1
  in
    (name, SOME n)
  end
