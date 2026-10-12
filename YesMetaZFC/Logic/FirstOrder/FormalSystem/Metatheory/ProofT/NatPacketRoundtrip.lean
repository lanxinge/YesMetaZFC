import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatPacket

/-! # 版本一自然数传输格式的往返定理 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket

def packBytes (bytes : List Nat) : Nat := bytes.foldr (fun byte rest => byte + 256 * rest) 1

theorem packBytes_pos (bytes : List Nat) : 0 < packBytes bytes := by
  induction bytes with
  | nil => decide
  | cons byte tail ih => simp only [packBytes, List.foldr_cons] at *; omega

theorem readBytes_pack (bytes : List Nat) (hBytes : ∀ b ∈ bytes, b < 256) (acc : List Nat) :
    readBytes (packBytes bytes) acc = some (acc.reverse ++ bytes) := by
  induction bytes generalizing acc with
  | nil =>
      rw [readBytes.eq_def]
      change some acc.reverse = some (acc.reverse ++ [])
      rw [List.append_nil]
  | cons byte tail ih =>
      have hb : byte < 256 := hBytes byte (by simp)
      have hp := packBytes_pos tail
      have he : packBytes (byte :: tail) = byte + 256 * packBytes tail := rfl
      have hdiv : (byte + 256 * packBytes tail) / 256 = packBytes tail := by omega
      have hmod : (byte + 256 * packBytes tail) % 256 = byte := by omega
      rw [readBytes.eq_def, he]
      rw [dif_neg (by omega)]
      rw [hdiv, hmod]
      rw [ih (fun b h => hBytes b (by simp [h]))]
      simp

theorem varint_bytes (n : Nat) : ∀ b ∈ varint n, b < 256 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rw [varint]
      split
      · intro b hb; simp only [List.mem_singleton] at hb; omega
      · rename_i h
        intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · have := Nat.mod_lt n (by decide : 0 < 128); omega
        · exact ih (n / 128) (Nat.div_lt_self (by omega) (by decide)) b hb

theorem readTokens_varint (n : Nat) (rest : List Nat) (value scale : Nat) (acc : List Nat)
    (hCanonical : scale ≠ 1 → n ≠ 0) :
    readTokens (varint n ++ rest) value scale acc =
      readTokens rest 0 1 ((value + n * scale) :: acc) := by
  induction n using Nat.strongRecOn generalizing value scale acc with
  | ind n ih =>
      rw [varint]
      split
      · rename_i h
        simp only [List.singleton_append, readTokens, h, ↓reduceIte]
        have hzero : ¬(scale != 1 && n == 0) = true := by simp; exact hCanonical
        simp [hzero]
      · rename_i h
        have hmod := Nat.mod_lt n (by decide : 0 < 128)
        have hpos : n / 128 ≠ 0 := by omega
        simp only [List.cons_append, readTokens,
          show ¬n % 128 + 128 < 128 by omega, ↓reduceIte, Nat.add_sub_cancel]
        rw [ih (n / 128) (Nat.div_lt_self (by omega) (by decide)) _ _ _ (fun _ => hpos)]
        have hn := Nat.mod_add_div n 128
        have he : value + n % 128 * scale + n / 128 * (scale * 128) = value + n * scale := by
          calc
            _ = value + (n % 128 + 128 * (n / 128)) * scale := by
              simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
            _ = _ := by rw [hn]
        rw [he]

theorem readTokens_flatMap (tokens : List Nat) (acc : List Nat) :
    readTokens (tokens.flatMap varint) 0 1 acc = some (acc.reverse ++ tokens) := by
  induction tokens generalizing acc with
  | nil =>
      change some acc.reverse = some (acc.reverse ++ [])
      rw [List.append_nil]
  | cons head tail ih =>
      simp only [List.flatMap_cons]
      rw [readTokens_varint head _ 0 1 acc (by simp)]
      simp only [Nat.mul_one, Nat.zero_add]
      rw [ih]
      simp

theorem weight_pos (tree : Tree) : 0 < tree.weight := by
  cases tree; simp only [Tree.weight]; omega

mutual
 theorem treeTokens_length (tree : Tree) : (treeTokens tree).length = 2 * tree.weight := by
  cases tree with
  | node tag children =>
      rw [treeTokens]
      simp only [List.length_cons, forestTokens_length children, Tree.weight]
      omega
 termination_by sizeOf tree

 theorem forestTokens_length (trees : List Tree) :
     (trees.flatMap treeTokens).length = 2 * (trees.map Tree.weight).sum := by
  cases trees with
  | nil => rfl
  | cons head tail =>
      simp only [List.flatMap_cons, List.length_append, treeTokens_length head,
        forestTokens_length tail, List.map_cons, List.sum_cons]
      omega
 termination_by sizeOf trees
end

mutual
 theorem readTree_treeTokens (tree : Tree) (rest : List Nat) (fuel : Nat)
     (hFuel : 2 * tree.weight ≤ fuel) :
     readTree fuel (treeTokens tree ++ rest) = some (tree, rest) := by
  cases tree with
  | node tag children =>
      cases fuel with
      | zero => exfalso; have := weight_pos (Tree.node tag children); omega
      | succ fuel =>
          rw [treeTokens]
          simp only [List.cons_append, readTree]
          rw [readForest_treeTokens children rest fuel (by simp only [Tree.weight] at hFuel; omega)]
          rfl
 termination_by sizeOf tree

 theorem readForest_treeTokens (trees : List Tree) (rest : List Nat) (fuel : Nat)
     (hFuel : 2 * (trees.map Tree.weight).sum + 1 ≤ fuel) :
     readForest fuel trees.length (trees.flatMap treeTokens ++ rest) = some (trees, rest) := by
  cases trees with
  | nil => simp [readForest]
  | cons head tail =>
      cases fuel with
      | zero => exfalso; omega
      | succ fuel =>
          have hp := weight_pos head
          simp only [List.map_cons, List.sum_cons] at hFuel
          simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readForest]
          rw [readTree_treeTokens head _ fuel (by omega)]
          dsimp
          rw [readForest_treeTokens tail rest fuel (by omega)]
          rfl
 termination_by sizeOf trees
end

/-- 任意有限原始树均能从其自然数编码完整恢复。 -/
@[simp] theorem decode_encode (tree : Tree) : decode (encode tree) = some tree := by
  unfold decode encode
  change (do
    let bytes ← readBytes (packBytes ((1 :: treeTokens tree).flatMap varint)) []
    let tokens ← readTokens bytes 0 1 []
    match tokens with
    | 1 :: payload => do
      let (tree, tail) ← readTree (payload.length + 1) payload
      if tail.isEmpty then some tree else none
    | _ => none) = some tree
  rw [readBytes_pack _ (by
    intro byte h
    obtain ⟨token, _, hToken⟩ := List.mem_flatMap.mp h
    exact varint_bytes token byte hToken)]
  dsimp
  rw [readTokens_flatMap]
  dsimp
  have h := readTree_treeTokens tree [] ((treeTokens tree).length + 1) (by rw [treeTokens_length]; omega)
  simp only [List.append_nil] at h
  change (readTree ((treeTokens tree).length + 1) (treeTokens tree)).bind (fun pair => if pair.2.isEmpty then some pair.1 else none) = some tree
  rw [h]
  rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket
