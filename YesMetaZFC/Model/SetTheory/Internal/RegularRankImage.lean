import YesMetaZFC.Model.SetTheory.Internal.SourceOmegaBound
import YesMetaZFC.SetTheory.Collapse.RegularRank

/-! # 正则秩图的完整初等像

原正则基数值在像中保持极限性和模型内正则性。全称量化搬运整张图，
故结论也适用于没有原像的尝试节点；不声称像高度在背景中仍为正则基数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem _root_.YesMetaZFC.SetTheory.Rr_d.image_l {ω c d X R Y S j A A' E E' η η' F F' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (algebra : Sc_algebra_d X) (aa : Rd_entry_d A A' j) (ee : Rd_entry_d E E' j)
    (hh : Rd_entry_d η η' j) (ff : Rd_entry_d F F' j) (rank : Rr_d I A E η F) :
    M.IsSetFunction I F' ∧ M.IsDomainOf I A' F' ∧
      (∀ a δ, Rd_entry_d a δ F' → M.IsLimitOrdinal δ ∧ Sc_regular_d Y δ ∧ M.mem η' δ) ∧
      ∀ a b δ ε, Rd_entry_d a b E' → Rd_entry_d a δ F' → Rd_entry_d b ε F' → M.mem δ ε := by
  obtain ⟨B, hB, coords⟩ := algebra.envelope_l (hj.1.1.input_mem_of_pairMember ff)
  have fn : Fn0_d A B F := fn0_of_function_l (ZF.modelsKP hZF)
    ⟨rank.function, rank.domain, fun a ha => by
      obtain ⟨δ, hd⟩ := (rank.domain a).mp ha
      exact ⟨δ, (coords a δ hd).2, hd⟩⟩
  obtain ⟨B', _, bb⟩ := hj.1.1.2.2 B hB
  have fn' := (hj.function_l hZF hω hX hY hm hn aa bb ff).mp fn
  -- 极限性和下界由同一个有界全称句子保持。
  let φ : Formula 1 4 := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 3)
    (.imp (rd_entry0_m (.bound 1) .newest (.bound 2)) (.conj (KP.limit0_m .newest) (.mem (.bound 3) .newest))))
  let ρ (A B η F : M.Domain) : Env M 4 := ⟨Fin.cases F (Fin.cases η (Fin.cases B (fun _ => A))), fun _ => A⟩
  have read A B η F : Formula.satisfies (ρ A B η F) φ ↔ ∀ a, M.mem a A → ∀ δ, M.mem δ B →
      Rd_entry_d a δ F → M.IsLimitOrdinal δ ∧ M.mem η δ := by
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_conj_iff, KP.limit0_sat_l (ZF.modelsKP hZF), Formula.satisfies_mem_iff]; rfl
  have tr := smap_delta_l I hZF hω hX hY hm hn hj φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.conj (KP.limit0_delta_l ..) (.mem ..)))))
    (ρ A B η F) (ρ A' B' η' F') (Fin.cases ff (Fin.cases hh (Fin.cases bb (fun _ => aa))))
  have limits := (read A' B' η' F').mp (tr.mp ((read A B η F).mpr
    (fun a _ δ _ hd => ⟨(rank.regular a δ hd).1.isLimitOrdinal, (rank.regular a δ hd).2⟩)))
  -- 外层量化所有模型内函数，覆盖目标中新出现的节点与小域函数。
  let ψ : Formula 1 4 := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 3)
    (.imp (rd_entry0_m (.bound 1) .newest (.bound 3))
      (Formula.forallMem .newest (sc_omega_bound_m .newest (.bound 1) (.bound 3)))))
  let θ (A B F : M.Domain) : Env M 3 := ⟨Fin.cases F (Fin.cases B (fun _ => A)), fun _ => A⟩
  have rs A B F f : Formula.satisfies ((θ A B F).push f) ψ ↔ ∀ a, M.mem a A → ∀ δ, M.mem δ B →
      Rd_entry_d a δ F → ∀ μ, M.mem μ δ → Fn0_d μ δ f →
        ∃ β, M.mem β δ ∧ ∀ n y, Rd_entry_d n y f → M.mem y β := by
    simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1, sc_omega_bound_sat_l hZF.1]; rfl
  have rt := hj.forall_delta_l hZF hω hX hY hm hn ψ (by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.forallMem _ (sc_omega_bound_delta_l ..)))))
    (θ A B F) (θ A' B' F') (Fin.cases ff (Fin.cases bb (fun _ => aa)))
  have regular f (hf : M.mem f Y) := (rs A' B' F' f).mp (rt.mp (fun f hf => (rs A B F f).mpr
    (fun a _ δ _ hd μ hμ => sc_regular_l hZF (rank.regular a δ hd).1 X μ hμ f hf)) f hf)
  -- 原下降不等式也整体搬运，不要求边的两个节点来自 j 的像。
  let χ : Formula 1 4 := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 4)
    (Formula.forallMem (.bound 4) (Formula.forallMem (.bound 5)
      (.imp (rd_entry0_m (.bound 3) (.bound 2) (.bound 5))
        (.imp (rd_entry0_m (.bound 3) (.bound 1) (.bound 4))
          (.imp (rd_entry0_m (.bound 2) .newest (.bound 4)) (.mem (.bound 1) .newest)))))))
  let ζ (A B E F : M.Domain) : Env M 4 := ⟨Fin.cases F (Fin.cases E (Fin.cases B (fun _ => A))), fun _ => A⟩
  have ds A B E F : Formula.satisfies (ζ A B E F) χ ↔ ∀ a, M.mem a A → ∀ b, M.mem b A →
      ∀ δ, M.mem δ B → ∀ ε, M.mem ε B → Rd_entry_d a b E → Rd_entry_d a δ F → Rd_entry_d b ε F → M.mem δ ε := by
    simp only [χ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  have dt := smap_delta_l I hZF hω hX hY hm hn hj χ (by simp -implicitDefEqProofs [χ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..)
      (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.mem ..))))))))
    (ζ A B E F) (ζ A' B' E' F') (Fin.cases ff (Fin.cases ee (Fin.cases bb (fun _ => aa))))
  have decrease := (ds A' B' E' F').mp (dt.mp ((ds A B E F).mpr (fun a _ b _ δ _ ε _ => rank.decrease a b δ ε)))
  exact ⟨(fn0_function_l (ZF.modelsKP hZF) fn').1, (fn0_function_l (ZF.modelsKP hZF) fn').2.1,
    fun a δ hd => ⟨(limits a (fn'.bound_l hd).1 δ (fn'.bound_l hd).2 hd).1,
      fun μ hμ f hf => regular f hf a (fn'.bound_l hd).1 δ (fn'.bound_l hd).2 hd μ hμ,
      (limits a (fn'.bound_l hd).1 δ (fn'.bound_l hd).2 hd).2⟩,
    fun a b δ ε hab ha hb => decrease a (fn'.bound_l ha).1 b (fn'.bound_l hb).1
      δ (fn'.bound_l ha).2 ε (fn'.bound_l hb).2 hab ha hb⟩

end YesMetaZFC.SetTheory.Internal
