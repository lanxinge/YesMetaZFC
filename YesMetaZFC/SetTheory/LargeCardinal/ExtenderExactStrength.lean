import YesMetaZFC.SetTheory.Notation
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedTransport
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankSource

/-! # 所属模型中的最大强度证书

用实际的 j(P(κ)) 读取支撑以下的子集覆盖。整个有界超幂和求值图均在所属
模型中构造；强度条款只量化该模型已有的子集，因而可随完整初等图传输。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Es_strength_d (X L Y : M.Domain) : Prop :=
  (∀ α, M.mem α L → ∀ x, M.mem x X → M.MemberSubset x α → M.mem x Y) ∧
    ∃ x, M.mem x X ∧ M.MemberSubset x L ∧ ¬ M.mem x Y

def es_strength_m {d} (L Y : Term d) : Formula 1 d := .conj
  (Formula.forallMem L (.forallE (.imp (Formula.subset .newest (.bound 1)) (.mem .newest Y.weaken.weaken))))
  (.existsE (.conj (Formula.subset .newest L.weaken) (.neg (.mem .newest Y.weaken))))
derive_free_closed es_strength_m

theorem es_strength_relative_l {X : M.Domain} (hX : M.TransitiveSet X)
    (nx : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X nx) d) (L Y : Term d) :
    Formula.satisfies ρ (es_strength_m L Y) ↔ Es_strength_d X (L.eval ρ).val (Y.eval ρ).val := by
  have sub {n} (η : Env (rt_model_l X nx) n) (a b : Term n) : Formula.satisfies η (Formula.subset a b) ↔
      M.MemberSubset (a.eval η).val (b.eval η).val := by
    simpa only [Formula.subset, Structure.MemberSubset, eval_image_env_l (M := rt_model_l X nx) (N := M) Subtype.val] using
      (rt_model_delta_l hX nx (.atom ..) η).trans (Formula.satisfies_subset_iff _ a b)
  simp only [es_strength_m, Es_strength_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, sub, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨lower, x, hx, missing⟩
    exact ⟨fun α hα y hy hyα => lower ⟨α, hX (L.eval ρ).val (L.eval ρ).property α hα⟩ hα ⟨y, hy⟩ hyα,
      x.val, x.property, hx, missing⟩
  · rintro ⟨lower, x, hx, sub, missing⟩
    exact ⟨fun α hα y hy => lower α.val hα y.val y.property hy, ⟨x, hx⟩, sub, missing⟩

theorem es_strength_map_l (hZF : M.Models ZF) {ω c d X R Y S j L L' B B' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (hL : Rd_entry_d L L' j) (hB : Rd_entry_d B B' j) : Es_strength_d X L B ↔ Es_strength_d Y L' B' := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨L, hj.1.1.input_mem_of_pairMember hL⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨L', hj.1.1.output_mem_of_pairMember hL⟩⟩
  let ρ : Env (rt_model_l X nx) 2 := ⟨Fin.cases ⟨B, hj.1.1.input_mem_of_pairMember hB⟩
    (fun _ => ⟨L, hj.1.1.input_mem_of_pairMember hL⟩), fun _ => ⟨L, hj.1.1.input_mem_of_pairMember hL⟩⟩
  let η : Env (rt_model_l Y ny) 2 := ⟨Fin.cases ⟨B', hj.1.1.output_mem_of_pairMember hB⟩
    (fun _ => ⟨L', hj.1.1.output_mem_of_pairMember hL⟩), fun _ => ⟨L', hj.1.1.output_mem_of_pairMember hL⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ hz, hn.empty_pred_l _ hz, hj⟩ nx ny
    (es_strength_m (.bound 1) .newest) (by simp -implicitDefEqProofs) ρ η (Fin.cases hB (fun _ => hL))
  exact (es_strength_relative_l hX nx ρ ..).symm.trans (tr.trans (es_strength_relative_l hY ny η ..))

/-- 相对幂集、有界节点、原测度关系与实际求值图共同刻画同一张扩展器的强度。 -/
def Ex_strength_d (hZF : M.Models ZF) (ω κ L X F : M.Domain) : Prop :=
  M.mem ω X ∧ M.mem κ X ∧ M.mem L X ∧ M.mem F X ∧ M.IsOrdinal L ∧
    ∃ K P A Q Y e, M.mem K X ∧ M.mem P X ∧ M.mem Y X ∧
      Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K ∧ FilterZF.Source_d X κ P ∧
      Eb_collapse_d ω κ L K X P F A Q Y e ∧ Es_strength_d X L Y

def es_strength0_m {d} (X L Y : Term d) : Formula 1 d := set[d] ⟪
  (∀ α ∈ ⌜L⌝ₛ, ∀ x ∈ ⌜X⌝ₛ, x ⊆ α → x ∈ ⌜Y⌝ₛ) ∧
  (∃ x ∈ ⌜X⌝ₛ, x ⊆ ⌜L⌝ₛ ∧ x ∉ ⌜Y⌝ₛ)⟫
derive_free_closed es_strength0_m

theorem es_strength0_delta_l {d} (X L Y : Term d) : (es_strength0_m X L Y).IsDelta0 :=
  .conj (.forallMem _ (.forallMem _ (.imp (.atom ..) (.mem ..))))
    (.existsMem _ (.conj (.atom ..) (.neg (.mem ..))))

theorem es_strength0_sat_l {d} (ρ : Env M d) (X L Y : Term d) :
    Formula.satisfies ρ (es_strength0_m X L Y) ↔ Es_strength_d (X.eval ρ) (L.eval ρ) (Y.eval ρ) := by
  simp only [es_strength0_m, Es_strength_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]; rfl

/-- 传输实际有界超幂、求值图以及相对最大强度，保留目标扩展器的全部证据。 -/
theorem Ex_strength_d.map_l (hZF : M.Models ZF) {ω c d X R Y S j κ κ' L L' F F' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω Y S)
    (hκ : Rd_entry_d κ κ' j) (hL : Rd_entry_d L L' j) (hF : Rd_entry_d F F' j)
    (h : Ex_strength_d hZF ω κ L X F) : Ex_strength_d hZF ω κ' L' Y F' := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨hωX, _, _, _, ho, K, P, A, Q, B, e, hK, hP, hB, seq, power, collapse, strength⟩ := h
  obtain ⟨hA, hQ, he⟩ : M.mem A X ∧ M.mem Q X ∧ M.mem e X := by
    obtain ⟨_, _, _, _, _, pool, _, _, _, hQ, he, _⟩ := collapse
    exact ⟨pool.carrier, hQ, he⟩
  obtain ⟨K', hK', hKK⟩ := hj.1.1.2.2 K hK
  obtain ⟨P', hP', hPP⟩ := hj.1.1.2.2 P hP
  obtain ⟨A', _, hAA⟩ := hj.1.1.2.2 A hA
  obtain ⟨Q', _, hQQ⟩ := hj.1.1.2.2 Q hQ
  obtain ⟨B', hB', hBB⟩ := hj.1.1.2.2 B hB
  obtain ⟨e', _, hee⟩ := hj.1.1.2.2 e he
  exact ⟨hj.1.1.output_mem_of_pairMember (hj.omega_l I hZF hω hX hY hm hn hωX),
    hj.1.1.output_mem_of_pairMember hκ, hj.1.1.output_mem_of_pairMember hL, hj.1.1.output_mem_of_pairMember hF,
    hj.ordinal_l hZF hω hX hY hm hn hL ho, K', P', A', Q', B', e', hK', hP', hB',
    hj.sequences_l hZF hω hX hY hm hn theory hωX hκ hKK seq,
    hj.power_l hZF hω hX hY hm hn hκ hPP power,
    collapse.map_l hZF hω hX hY hm hn hj theory hωX hκ hL hKK hPP hF hAA hQQ hBB hee,
    (es_strength_map_l hZF hω hX hY hm hn hj hL hBB).mp strength⟩

/-- 源内证书读取指定实际超幂的最大强度，不要求它在背景中不可达。 -/
theorem Ex_strength_d.realize_l (hZF : M.Models ZF) {ω κ K L X R F c d N S j Γ : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d N S)
    (ultra : It_ultra_d hZF ω κ L F c d j) (hκ : M.TransitiveSet κ)
    (hκj : Rd_entry_d κ Γ j) (bound : M.MemberSubset L Γ)
    (h : Ex_strength_d hZF ω κ L X F) : Es_strength_d X L N := by
  obtain ⟨_, _, _, _, _, K₀, P, A, Q, Y, e, _, hP, _, seq, power, collapse, strength⟩ := h
  have eq := hZF.1.eq_of_same_members K₀ K (fun s => (seq s).trans (source.finite s).symm)
  subst K₀
  have trans : M.TransitiveSet P := by
    intro x hx y hy
    have hyκ := ((power x).mp hx).2 y hy
    exact (power y).mpr ⟨source.transitive κ source.cardinal_mem y hyκ, hκ y hyκ⟩
  have hPY := (collapse.image_l hZF source family hm hn ultra hP trans).1
  have hj := ultra.elementary_l hZF hm.1 hn.1
  have hN := ultra.transitive_l hZF hn.1
  have target := hj.power_l hZF source.omega source.transitive hN hm hn hκj hPY power
  refine ⟨fun α hα x hx sub => hN Y (hj.1.1.output_mem_of_pairMember hPY) x (strength.1 α hα x hx sub), ?_⟩
  obtain ⟨x, hx, sub, missing⟩ := strength.2
  exact ⟨x, hx, sub, fun hxN => missing ((target x).mpr ⟨hxN, fun y hy => bound y (sub y hy)⟩)⟩

theorem ep_exact_strength_l (hZFC : M.Models ZFC) {ω κ K L X R F δ V b d N S i Γ : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) (hδ : M.IsLimitOrdinal δ)
    (hL : M.mem L δ) (hκL : M.mem κ L) (hωL : M.mem ω L)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L)
    (hV : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L V)
    (family : Em_source_d ω κ L X F) (hF : M.mem F X)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) b X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (ultra : It_ultra_d (ZFC.models_zf_l hZFC) ω κ L F b d i)
    (hκi : Rd_entry_d κ Γ i) (bound : M.MemberSubset L Γ) (cover : M.MemberSubset V N)
    (missing : ∃ x, M.MemberSubset x L ∧ ¬ M.mem x N) :
    Ex_strength_d (ZFC.models_zf_l hZFC) ω κ L X F ∧ Er_level_d X L V := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hN := ultra.transitive_l hZF hn.1
  have hi := ultra.elementary_l hZF hm.1 hn.1
  have hLX := ZF.v_ordinal_mem_l I hZF hX hL
  have level := ep_relative_rank_l hZFC source hX hδ hL hωL hr hs hV
  have hκV := ZF.v_ordinal_mem_l I hZF hV hκL
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF κ
  have hPX := ZF.v_power_mem_l I hZF hX hδ source.cardinal_mem hP
  have trans : M.TransitiveSet P := fun x hx y hy => (hP y).mpr
    ((hr.isCardinal.1.mem hκL).transitive y ((hP x).mp hx y hy))
  obtain ⟨Y, hYN, hPY⟩ := hi.1.1.2.2 P hPX
  obtain ⟨hYX, A, Q, e, collapse⟩ := it_ultra_owned_image_l hZF source (sc_v_power_l hZF hδ hX)
    family hm hn ultra hLX hF hr.isLimitOrdinal level hκV
    (ZF.v_power_mem_l I hZF hV hr.isLimitOrdinal hκV hP) trans hPY
  have powers : FilterZF.Source_d X κ P := fun x =>
    ⟨fun hx => ⟨source.transitive P hPX x hx, (hP x).mp hx⟩, fun ⟨_, hx⟩ => (hP x).mpr hx⟩
  have power := hi.power_l hZF source.omega source.transitive hN hm hn hκi hPY powers
  refine ⟨⟨source.omega_mem, source.cardinal_mem, hLX, hF, hr.isCardinal.1,
    K, P, A, Q, Y, e, source.finite_mem, hPX, hYX, source.finite, powers, collapse, ?_, ?_⟩, level⟩
  · intro α hα x _ sub
    have hxN := cover x (ZF.v_subset_mem_l I hZF hV (ZF.v_ordinal_mem_l I hZF hV hα) sub)
    exact (power x).mpr ⟨hxN, fun y hy => bound y (hr.isCardinal.1.transitive α hα y (sub y hy))⟩
  · obtain ⟨x, sub, hx⟩ := missing
    exact ⟨x, ZF.v_subset_mem_l I hZF hX hLX sub, sub, fun h => hx (hN Y hYN x h)⟩

end YesMetaZFC.SetTheory.LargeCardinal
