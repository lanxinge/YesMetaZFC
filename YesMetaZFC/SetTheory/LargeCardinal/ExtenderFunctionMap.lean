import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFunctionCode
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopyComponent
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSetCode

/-! # 两张图在 κ 值代表函数上相同

给函数值追加一个坐标，得到有限 κ 幂的源子集。两图搬运同一编码，
再由有界解码方程恢复同一函数图；不另假设代表函数的像一致。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ea_maps_d.function_l {ω κ κ' K K₀ X R Y S N R₀ N' R₁ c d b b' π σ n D f f' : M.Domain}
    (maps : Ea_maps_d ω κ X π σ) (source : Ep_source_d hZF ω κ K X R)
    (owner : Ep_source_d hZF ω κ K₀ N R₀) (hY : M.TransitiveSet Y) (hN' : M.TransitiveSet N')
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁) (hσ : Smap_d I ω b b' N N' σ)
    (hκπ : Rd_entry_d κ κ' π) (hκσ : Rd_entry_d κ κ' σ)
    (hnω : M.mem n ω) (space : Ep_space_d κ n D) (hfX : M.mem f X) (fn : Fn0_d D κ f)
    (hff : Rd_entry_d f f' π) : Rd_entry_d f f' σ := by
  have sub : Ea_subset_d ω κ X N := by
    intro n D A hn hd bound hA
    obtain ⟨A', _, hAA⟩ := hπ.1.1.2.2 A hA
    exact hσ.1.1.input_mem_of_pairMember (maps n D A A' hn hd hA bound hAA)
  have hfN := sub.function_l hZF source owner hnω space hfX fn
  obtain ⟨f'', _, hff''⟩ := hσ.1.1.2.2 f hfN
  obtain ⟨m, E, A, hmω, _, hE, hAX, bound, read⟩ := ep_function_code_l hZF source hnω space hfX fn
  obtain ⟨A', _, hAA⟩ := hπ.1.1.2.2 A hAX
  have hAσ := maps m E A A' hmω hE hAX bound hAA
  have hDX := source.space_mem_l hZF hnω space
  obtain ⟨D', _, hDD⟩ := hπ.1.1.2.2 D hDX
  have hDσ := maps n D D D' hnω space hDX (fun _ h => h) hDD
  have nπ := hπ.natural_l hZF source.omega source.transitive hY hm hn source.omega_mem n hnω
  have nσ := hσ.natural_l hZF source.omega owner.transitive hN' h₀ h₁ owner.omega_mem n hnω
  let φ : Formula 1 5 := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 3)
    (.iff (rd_entry0_m (.bound 1) .newest (.bound 2)) (Formula.existsMem (.bound 3)
      (.conj (Formula.subset (.bound 2) .newest) (rd_entry0_m (.bound 7) (.bound 1) .newest)))))
  have closed : φ.FreeClosed := by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]
  have delta : φ.IsDelta0 := .forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..)
    (.existsMem _ (.conj (.atom ..) (rd_entry0_delta_l ..)))))
  let ρ : Env M 5 := ⟨Fin.cases f (Fin.cases A (Fin.cases κ (Fin.cases D (fun _ => n)))), fun _ => n⟩
  have tr := smap_delta_l I hZF source.omega source.transitive hY hm hn hπ φ closed delta ρ
    ⟨Fin.cases f' (Fin.cases A' (Fin.cases κ' (Fin.cases D' (fun _ => n)))), fun _ => n⟩
    (Fin.cases hff (Fin.cases hAA (Fin.cases hκπ (Fin.cases hDD (fun _ => nπ)))))
  have tr' := smap_delta_l I hZF source.omega owner.transitive hN' h₀ h₁ hσ φ closed delta ρ
    ⟨Fin.cases f'' (Fin.cases A' (Fin.cases κ' (Fin.cases D' (fun _ => n)))), fun _ => n⟩
    (Fin.cases hff'' (Fin.cases hAσ (Fin.cases hκσ (Fin.cases hDσ (fun _ => nσ)))))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_subset_iff, rd_entry0_sat_l hZF.1] at tr tr'
  have spec t (ht : M.mem t D) x (hx : M.mem x κ) : Rd_entry_d t x f ↔
      ∃ s, M.mem s A ∧ M.MemberSubset t s ∧ Rd_entry_d n x s :=
    (read t x).trans ⟨fun h => h.2.2, fun h => ⟨ht, hx, h⟩⟩
  have decode := tr.mp spec
  have decode' := tr'.mp spec
  have fn' := (hπ.function_l hZF source.omega source.transitive hY hm hn hDD hκπ hff).mp fn
  have fn'' := (hσ.function_l hZF source.omega owner.transitive hN' h₀ h₁ hDσ hκσ hff'').mp fn
  have eq : f' = f'' := fn'.ext_l hZF.1 fn'' (fun t ht => by
    obtain ⟨x, hx, htx⟩ := fn'.2.1 t ht
    exact ⟨x, htx, (decode' t ht x hx).mpr ((decode t ht x hx).mp htx)⟩)
  exact eq.symm ▸ hff''

/-- 两图搬运相同的成员编码，故在有限 κ 幂子集值函数上也相同。 -/
theorem Ea_maps_d.set_function_l {ω κ κ' K K₀ X R Y S N R₀ N' R₁ c d b b' π σ n m D E f f' : M.Domain}
    (maps : Ea_maps_d ω κ X π σ) (source : Ep_source_d hZF ω κ K X R)
    (owner : Ep_source_d hZF ω κ K₀ N R₀) (hY : M.TransitiveSet Y) (hN' : M.TransitiveSet N')
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁) (hσ : Smap_d I ω b b' N N' σ)
    (hκπ : Rd_entry_d κ κ' π) (hκσ : Rd_entry_d κ κ' σ)
    (hnω : M.mem n ω) (hmω : M.mem m ω) (hd : Ep_space_d κ n D) (he : Ep_space_d κ m E)
    (hfX : M.mem f X) (fn : Fn0_d D X f) (bound : ∀ t B, Rd_entry_d t B f → M.MemberSubset B E)
    (hff : Rd_entry_d f f' π) : Rd_entry_d f f' σ := by
  have sub : Ea_subset_d ω κ X N := by
    intro n D A hn hd bound hA
    obtain ⟨A', _, hAA⟩ := hπ.1.1.2.2 A hA
    exact hσ.1.1.input_mem_of_pairMember (maps n D A A' hn hd hA bound hAA)
  have hfN := sub.set_function_l hZF source owner hnω hmω hd he hfX fn bound
  obtain ⟨f'', _, hff''⟩ := hσ.1.1.2.2 f hfN
  obtain ⟨l, q, r, H, A, hl, hq, hr, hH, hAX, hs, read⟩ :=
    ep_set_function_code_l hZF source hnω hmω hd he hfX fn bound
  obtain ⟨A', _, hAA⟩ := hπ.1.1.2.2 A hAX
  have hAσ := maps l H A A' hl hH hAX hs hAA
  have hDX := source.space_mem_l hZF hnω hd
  have hEX := source.space_mem_l hZF hmω he
  obtain ⟨D', _, hDD⟩ := hπ.1.1.2.2 D hDX
  obtain ⟨E', _, hEE⟩ := hπ.1.1.2.2 E hEX
  have hDσ := maps n D D D' hnω hd hDX (fun _ h => h) hDD
  have hEσ := maps m E E E' hmω he hEX (fun _ h => h) hEE
  have natπ := hπ.natural_l hZF source.omega source.transitive hY hm hn source.omega_mem
  have natσ := hσ.natural_l hZF source.omega owner.transitive hN' h₀ h₁ owner.omega_mem
  have finite k g (hk : M.mem k ω) (hg : Fn0_d k ω g) : M.mem g X ∧ M.mem g N := by
    have fk := fn0_function_l (ZF.modelsKP hZF) (hg.mono_target_l source.below)
    exact ⟨source.transitive K source.finite_mem g ((source.finite g).mpr ⟨k, hk, fk⟩),
      owner.transitive K₀ owner.finite_mem g ((owner.finite g).mpr ⟨k, hk, fk⟩)⟩
  have qω := hq.mono_target_l (source.omega.transitive hZF l hl)
  have rω := hr.mono_target_l (source.omega.transitive hZF l hl)
  have qπ := hπ.finite_fixed_l hZF source.omega source.transitive hY hm hn source.omega_mem hnω (finite n q hnω qω).1 qω
  have rπ := hπ.finite_fixed_l hZF source.omega source.transitive hY hm hn source.omega_mem hmω (finite m r hmω rω).1 rω
  have qσ := hσ.finite_fixed_l hZF source.omega owner.transitive hN' h₀ h₁ owner.omega_mem hnω (finite n q hnω qω).2 qω
  have rσ := hσ.finite_fixed_l hZF source.omega owner.transitive hN' h₀ h₁ owner.omega_mem hmω (finite m r hmω rω).2 rω
  -- 外层只量化源内的函数值；比较时不要求两图已在值域集合上一致。
  let φ : Formula 1 11 := Formula.forallMem (.bound 9)
    (.imp (rd_entry0_m .newest (.bound 1) (.bound 2))
      (.conj (Formula.subset (.bound 1) (.bound 11)) (Formula.forallMem (.bound 11)
        (.iff (.mem .newest (.bound 2))
          (ep_pair_at_m (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 4) (.bound 1) .newest)))))
  have closed : φ.FreeClosed := by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]
  have delta : φ.IsDelta0 := .forallMem _ (.imp (rd_entry0_delta_l ..)
    (.conj (.atom ..) (.forallMem _ (.iff (.mem ..) (ep_pair_at_delta_l ..)))))
  let ρ : Env M 10 := ⟨Fin.cases f (Fin.cases A (Fin.cases κ (Fin.cases n (Fin.cases m
    (Fin.cases l (Fin.cases q (Fin.cases r (Fin.cases D (fun _ => E))))))))), fun _ => E⟩
  have tr := hπ.forall_delta_l hZF source.omega source.transitive hY hm hn φ closed delta ρ
    ⟨Fin.cases f' (Fin.cases A' (Fin.cases κ' (Fin.cases n (Fin.cases m
      (Fin.cases l (Fin.cases q (Fin.cases r (Fin.cases D' (fun _ => E'))))))))), fun _ => E'⟩
    (Fin.cases hff (Fin.cases hAA (Fin.cases hκπ (Fin.cases (natπ n hnω) (Fin.cases (natπ m hmω)
      (Fin.cases (natπ l hl) (Fin.cases qπ (Fin.cases rπ (Fin.cases hDD (fun _ => hEE))))))))))
  have tr' := hσ.forall_delta_l hZF source.omega owner.transitive hN' h₀ h₁ φ closed delta ρ
    ⟨Fin.cases f'' (Fin.cases A' (Fin.cases κ' (Fin.cases n (Fin.cases m
      (Fin.cases l (Fin.cases q (Fin.cases r (Fin.cases D' (fun _ => E'))))))))), fun _ => E'⟩
    (Fin.cases hff'' (Fin.cases hAσ (Fin.cases hκσ (Fin.cases (natσ n hnω) (Fin.cases (natσ m hmω)
      (Fin.cases (natσ l hl) (Fin.cases qσ (Fin.cases rσ (Fin.cases hDσ (fun _ => hEσ))))))))))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hZF.1, ep_pair_at_sat_l hZF.1] at tr tr'
  have decode := tr.mp (fun B _ t _ htB => ⟨bound t B htB, fun x _ => read t B htB x⟩)
  have decode' := tr'.mp (fun B _ t _ htB => ⟨bound t B htB, fun x _ => read t B htB x⟩)
  have fn' := (hπ.sfun_l hZF source.omega source.transitive hY hm hn hDD hff
    (source.function_l hZF hfX fn)).function_l hY
  have fnN := fn.retarget_l (fun t B htB => (rd_entry_transitive_l owner.transitive hfN htB).2)
  have fn'' := (hσ.sfun_l hZF source.omega owner.transitive hN' h₀ h₁ hDσ hff''
    (owner.function_l hZF hfN fnN)).function_l hN'
  have eq : f' = f'' := fn'.ext_l hZF.1 fn'' (fun t ht => by
    obtain ⟨B, hB, htB⟩ := fn'.2.1 t ht
    obtain ⟨C, hC, htC⟩ := fn''.2.1 t ht
    obtain ⟨bB, dB⟩ := decode B hB t ht htB
    obtain ⟨bC, dC⟩ := decode' C hC t ht htC
    have eq := hZF.1.eq_of_same_members B C fun x =>
      ⟨fun hx => (dC x (bB x hx)).mpr ((dB x (bB x hx)).mp hx),
        fun hx => (dB x (bC x hx)).mpr ((dC x (bC x hx)).mp hx)⟩
    exact ⟨B, htB, eq.symm ▸ htC⟩)
  exact eq.symm ▸ hff''

end YesMetaZFC.SetTheory.LargeCardinal
