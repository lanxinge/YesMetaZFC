import YesMetaZFC.SetTheory.LargeCardinal.ExtenderNormalSyntax

/-! # 派生有限支撑测度的正规性

若 f(s)<s(i) 在 U_a 上几乎处处成立，则 β=j(f)(a)<a(i)。把 β 添入支撑，
由 f 的图的初等性得到 f(s↾n)=s(n) 几乎处处成立。只使用 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}}

theorem es_normal_l (hZF : M.Models ZF) {ω δ X C Y E j κ k L S F : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X C Y E j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k) (hL : M.IsOrdinal L)
    (hLk : M.MemberSubset L k) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F) :
    En_normal_d ω κ L F := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := ZF.v_transitive_l I hZF hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  have small n (hn : M.mem n ω) := hc.ordinal.transitive ω hωκ n hn
  have space n D (hn : M.mem n ω) (hd : ∀ s, M.mem s D ↔ Fn0_d n κ s) : M.mem D X :=
    ZF.v_function_space_mem_l I hZF hX hδ hc.source (hc.ordinal.transitive n (small n hn))
      (fun s => (hd s).trans ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩)
  intro n a U D f i α A hn ha haU hD hf hiα hAU below
  obtain ⟨_, n', D₀, hn', hD₀, hu⟩ := (hF.2.2 a U).mp haU
  have en := hn'.domain_eq_l hZF.1 ha
  subst n'
  have eD := hZF.1.eq_of_same_members D₀ D (fun s => (hD₀ s).trans (hD s).symm)
  subst D₀
  obtain ⟨D', _, hjD⟩ := hj.2.2 D (space n D hn hD)
  obtain ⟨W, hWX, hDW, hκW⟩ := ZF.v_joint_bound_l I hZF hX (space n D hn hD) hc.source
  have hfX := ZF.v_relation_mem_l I hZF hX hδ hWX (F := f) (fun p hp => by
    obtain ⟨s, hs, x, hx, hp⟩ := hf.1 p hp
    exact ⟨s, hDW s hs, x, hκW x hx, hp⟩)
  obtain ⟨f', _, hjf⟩ := hj.2.2 f hfX
  have hff := (spred_function_l I hZF hω h ht hY hjD hc.image hjf).mp hf
  have haY := hSY a ((hF.2.2 a U).mp haU).1
  have haD := es_seed_l I hZF hω h ht hY (hc.fixed n (small n hn)) hc.image hjD hD hLk haY ha
  obtain ⟨β, hβk, haβ⟩ := hff.2.1 a haD
  obtain ⟨_, A', hjA, haA⟩ := (hu A).mp hAU
  let φ : Formula 1 4 := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 3)
    (Formula.forallMem (.bound 4) (.imp (.conj (rd_entry0_m (.bound 2) (.bound 1) (.bound 4))
      (rd_entry0_m (.bound 3) .newest (.bound 2))) (.mem (.bound 1) .newest))))
  have tr := spred_delta_l I hZF hω h ht hY φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.forallMem _ (.forallMem _ (.imp (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)) (.mem _ _)))))
    ⟨Fin.cases i (Fin.cases f (Fin.cases κ (fun _ => A))), fun _ => n⟩
    ⟨Fin.cases i (Fin.cases f' (Fin.cases k (fun _ => A'))), fun _ => n⟩
    (Fin.cases (hc.fixed i (hc.ordinal.transitive n (small n hn) i (ha.bound_l hiα).1))
      (Fin.cases hjf (Fin.cases hc.image (fun _ => hjA))))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff] at tr
  have hβα : M.mem β α := tr.mp (fun s hs x _ y _ hh => below s hs x y hh.1 hh.2)
    a haA β hβk α (hLk α (ha.bound_l hiα).2) ⟨haβ, hiα⟩
  obtain ⟨m, b, hm, hb, m', n', endb⟩ := ZF.fseq_end_exists_l I hZF hω hn
    (fn0_function_l (ZF.modelsKP hZF) ha) (hL.transitive α (ha.bound_l hiα).2 β hβα)
  have em := endb.source.2.2.2.eq hZF.1 hb.2.1
  subst m'
  have en := endb.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) ha).2.1
  subst n'
  have hab : M.MemberSubset a b := fun p hp => by
    obtain ⟨i, _, x, _, hpi⟩ := ha.1 p hp
    obtain ⟨q, hq, hqb⟩ := ((endb.prefix_restriction.2 i x).mp ⟨p, hpi, hp⟩).2
    exact (I.unique hpi hq) ▸ hqb
  obtain ⟨V, hbV⟩ := (hF.2.1 b).mp ((hS b).mpr ⟨m, hm, hb⟩)
  obtain ⟨_, m', H, hm', hH, hv⟩ := (hF.2.2 b V).mp hbV
  have em := hm'.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hb)
  subst m'
  obtain ⟨H', _, hjH⟩ := hj.2.2 H (space m H hm hH)
  let ρ : Env M 4 := ⟨Fin.cases f (Fin.cases A (Fin.cases κ (fun _ => n))), fun _ => n⟩
  let ψ : UnarySchema 4 := { body := en_graph_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨B, hs⟩ := ZF.separation_exists_d hZF ψ ρ H
  have spec s : M.mem s B ↔ M.mem s H ∧ En_graph_d n κ A f s :=
    (hs s).trans (and_congr_right fun _ => en_graph_sat_l hZF.1 _ _ _ _ _ _)
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF H
  have hBX := ht P (ZF.v_power_mem_l I hZF hX hδ (space m H hm hH) hP) B
    ((hP B).mpr fun s hs => ((spec s).mp hs).1)
  obtain ⟨B', _, hjB⟩ := hj.2.2 B hBX
  let θ : Formula 1 6 := Formula.forallMem (.bound 5) (.iff (.mem .newest (.bound 5))
    (en_graph_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))
  have transfer := spred_delta_l I hZF hω h ht hY θ (by simp -implicitDefEqProofs [θ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.iff (.mem _ _) (en_graph_delta_l ..)))
    ⟨Fin.cases f (Fin.cases A (Fin.cases κ (Fin.cases n (Fin.cases B (fun _ => H))))), fun _ => n⟩
    ⟨Fin.cases f' (Fin.cases A' (Fin.cases k (Fin.cases n (Fin.cases B' (fun _ => H'))))), fun _ => n⟩
    (Fin.cases hjf (Fin.cases hjA (Fin.cases hc.image (Fin.cases (hc.fixed n (small n hn)) (Fin.cases hjB (fun _ => hjH))))))
  simp only [θ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, en_graph_sat_l hZF.1] at transfer
  have hbH := es_seed_l I hZF hω h ht hY (hc.fixed m (small m hm)) hc.image hjH hH hLk
    (hSY b ((hS b).mpr ⟨m, hm, hb⟩)) (fn0_of_function_l (ZF.modelsKP hZF) hb)
  have hbB := (transfer.mp (fun s hs => (spec s).trans ⟨And.right, fun hh => ⟨hs, hh⟩⟩) b hbH).mpr
    ⟨a, haA, hab, β, hβk, haβ, endb.last_value⟩
  exact ⟨m, b, V, β, B, hm, endb.length_successor, fn0_of_function_l (ZF.modelsKP hZF) hb,
    hab, endb.last_value, hβα, hbV, (hv B).mpr ⟨fun s hs => ((spec s).mp hs).1, B', hjB, hbB⟩,
    fun s hs => ((spec s).mp hs).2⟩

end YesMetaZFC.SetTheory.LargeCardinal
