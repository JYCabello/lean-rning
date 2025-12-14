def List.sumOfContents [Add α] [zero : Zero α] : List α -> α :=
  λ lst =>
    let rec sum l (acc : α) :=
      match l with
      | [] => acc
      | x :: xs => sum xs (x + acc)
    sum lst zero.zero


#eval [1, 2, 3].sumOfContents
