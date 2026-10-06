import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessibleRank
import YesMetaZFC.Model.SetTheory.Internal.SourceRankSize
import YesMetaZFC.Model.SetTheory.Internal.SourceOmegaBound

/-! # 任意内部不可达支撑的正则界与秩层枚举

该原一阶句子在初始秩模型中实际成立，完整初等图可双向传输它。因此每个
后继中新出现的不可达序数也取得小秩层枚举和正则函数界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_inaccessible_closure_d (I : kpair_convention_l.Interpretation M) (ω X : M.Domain) : Prop :=
  ∀ L, Sc_inaccessible_d ω X L → Sc_regular_d X L ∧ Sc_rank_size_d I X L

def sc_inaccessible_closure_m {d} (ω : Term d) : Formula 1 d := .forallE
  (.imp (sc_inaccessible_m ω.weaken .newest) (.conj
    (Formula.forallMem .newest (.forallE (sc_omega_bound_m (.bound 1) (.bound 2) .newest)))
    (sc_rank_size_m .newest)))
derive_free_closed sc_inaccessible_closure_m

theorem sc_inaccessible_closure_sat_l (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
    (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (nx : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X nx) d) (ω : Term d) :
    Formula.satisfies ρ (sc_inaccessible_closure_m ω) ↔
      Sc_inaccessible_closure_d (kp_pair_l hKP) (ω.eval ρ).val X := by
  have bound {n} (η : Env (rt_model_l X nx) n) (μ L f : Term n) :
      Formula.satisfies η (sc_omega_bound_m μ L f) ↔ (Fn0_d (μ.eval η).val (L.eval η).val (f.eval η).val →
        ∃ β, M.mem β (L.eval η).val ∧ ∀ i y, Rd_entry_d i y (f.eval η).val → M.mem y β) := by
    simpa only [eval_image_env_l (M := rt_model_l X nx) (N := M) Subtype.val] using
      (rt_model_delta_l hX nx (sc_omega_bound_delta_l ..) η).trans (sc_omega_bound_sat_l hKP.1 ..)
  simp only [sc_inaccessible_closure_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    sc_inaccessible_sat_l hKP.1 hX hp nx, sc_rank_size_sat_l hKP hX nx, bound, Definitional.Term.eval_weaken]
  constructor
  · intro all L hL
    have copy := hL
    obtain ⟨_, hLX, _⟩ := copy
    obtain ⟨regular, sizes⟩ := all ⟨L, hLX⟩ hL
    exact ⟨fun μ hμ f hf => regular ⟨μ, hX L hLX μ hμ⟩ hμ ⟨f, hf⟩, sizes⟩
  · intro all L hL
    obtain ⟨regular, sizes⟩ := all L.val hL
    exact ⟨fun μ hμ f => regular μ.val hμ f.val f.property, sizes⟩

theorem sc_inaccessible_closure_iff_l (hZF : M.Models ZF) {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (px : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (py : ∀ a b, M.mem a Y → M.mem b Y → ∃ p, M.mem p Y ∧ Pair_d M p a b)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) (hωX : M.mem ω X) :
    Sc_inaccessible_closure_d (kp_pair_l (ZF.modelsKP hZF)) ω X ↔
      Sc_inaccessible_closure_d (kp_pair_l (ZF.modelsKP hZF)) ω Y := by
  have hw := hj.omega_l _ hZF hω hX hY hm hn hωX
  have hωY := hj.1.1.output_mem_of_pairMember hw
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hωX⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω, hωY⟩⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ⟨ω, hωX⟩, fun _ => ⟨ω, hωX⟩⟩
  let η : Env (rt_model_l Y ny) 1 := ⟨fun _ => ⟨ω, hωY⟩, fun _ => ⟨ω, hωY⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ hz, hn.empty_pred_l _ hz, hj⟩ nx ny
    (sc_inaccessible_closure_m .newest) (by simp -implicitDefEqProofs) ρ η (fun _ => hw)
  exact (sc_inaccessible_closure_sat_l (ZF.modelsKP hZF) hX px nx ρ .newest).symm.trans
    (tr.trans (sc_inaccessible_closure_sat_l (ZF.modelsKP hZF) hY py ny η .newest))

theorem Sc_inaccessible_closure_d.rank_l (hZF : M.Models ZF) {ω X α V : M.Domain}
    (hX : M.TransitiveSet X) (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (hV : M.mem V X) (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α)
    (h : Sc_inaccessible_closure_d (kp_pair_l (ZF.modelsKP hZF)) ω X) :
    Sc_inaccessible_closure_d (kp_pair_l (ZF.modelsKP hZF)) ω V := by
  intro L inaccessible
  obtain ⟨regular, sizes⟩ := h L (inaccessible.of_rank_l hZF hX hp hV rank hα)
  obtain ⟨_, hL, _⟩ := inaccessible
  exact ⟨fun μ hμ f hf => regular μ hμ f (hX V hV f hf), sizes.rank_l hZF hX hV rank hα hL⟩

end YesMetaZFC.SetTheory.Internal
