import YesMetaZFC.SetTheory.LargeCardinal.TypeGameLimitValues

/-! # 控制参数在偶数极限中相同

相邻控制参数沿原偶数边搬运，锥的交换律使它们在目标中的像相等。
对真实像函数作内部 ω 关系归纳，得到统一的目标控制树及字母表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.control_const_l {ω c o C γ Z A D f B d N W P : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (branch : ∀ x, M.mem x B ↔ Tg_even_d f (U 0) x)
    (cone : It_embedding_d hZF ω B (U 1) (U 2) d N W P) (a : Fin 19) :
    ∃ z, M.mem z N ∧ ∀ i x, Tg_limit_value_d (a.castAdd 27) f P i x → x = z := by
  obtain ⟨F, ff, fs⟩ := h.limit_values_l hZF tree columns branch cone (a.castAdd 27)
  have step i j x y (succ : M.SuccessorOf j i) (hx : Rd_entry_d i x F) (hy : Rd_entry_d j y F) : x = y := by
    obtain ⟨v, s, r, hs, ps, hr, hx⟩ := (fs i x).mp hx
    obtain ⟨w, t, l, ht, pt, hl, hy⟩ := (fs j y).mp hy
    have next := (h.steps i j s t succ hs ht).read_l hZF ps pt
    obtain ⟨_, _, _, _, _, _, _, k, _, _, _, _, _, _, edge, control, _⟩ := next
    have edge : It_map_d (U 2) (v 7) (w 7) k := by
      obtain ⟨b, bp, q, qp, hq⟩ := edge
      exact ⟨b, bp, q, qp, (columns 2 q).mpr ⟨w, j, t, ht, pt, hq⟩⟩
    have node : Rd_entry_d (v 7) (v 15) (U 1) := by
      obtain ⟨q, qp, hq⟩ := (h.read_l hZF hs ps).1.node
      exact ⟨q, qp, (columns 1 q).mpr ⟨v, i, s, hs, ps, hq⟩⟩
    have elem := cone.elementary (v 7) r (v 15) (v 0) (v 1) hr node (h.read_l hZF hs ps).1.model.1
    exact elem.1.1.1.2 _ x y hx (cone.commute (v 7) (w 7) k r l edge hr hl _ _ y (control a) hy)
  let η : Env M 0 := ⟨Fin.elim0, fun _ => F⟩
  let φ : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  have eqv x y : φ.denote η x y ↔ x = y := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  have all := ZF.rel_chain_l I hZF φ η tree.tree.omega (fn0_function_l (ZF.modelsKP hZF) ff)
    (fun _ _ _ _ _ _ hx hy => (eqv _ _).mpr (((eqv _ _).mp hx).trans ((eqv _ _).mp hy)))
    (fun i j x y succ hx hy => (eqv _ _).mpr (step i j x y succ hx hy))
  obtain ⟨e, he, heω⟩ := tree.tree.omega.1.1
  obtain ⟨z, hz, first⟩ := ff.2.1 e heω
  refine ⟨z, hz, fun i x hx => ?_⟩
  have hx := (fs i x).mpr hx
  rcases (tree.tree.omega.isOrdinal hZF).wellOrder.linear.compare e heω i (ff.bound_l hx).1 with eq | ei | ie
  · have eq := hZF.1.eq_of_same_members e i eq
    exact (fn0_function_l (ZF.modelsKP hZF) ff).1.2 i x z hx (eq ▸ first)
  · exact ((eqv z x).mp (all e i z x ei first hx)).symm
  · exact (he i ie).elim

end YesMetaZFC.SetTheory.LargeCardinal
