import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.TreeSyntax
import YesMetaZFC.Model.SetTheory.Types.SubtypeUp

/-! # 原关系树的实际所属强度证书

每条活动边保留所属模型中的同一有界秩源、扩展器、不可达支撑和最大强度。
这些判断使用原关系，不把支撑对象码当成背景序数。恒等填充不添加活动证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def it_native_quality_m {d} (ω κ L F : Term d) : Formula 1 d := set[d] ⟪
  ∃ δ X K R, ⌜v_sigma_m⌝ₚ(δ,X) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(δ) ∧
    ⌜ep_source_m⌝ₚ(⌜ω⌝ₛ,⌜κ⌝ₛ,K,X,R) ∧ ⌜ex_quality_m⌝ₚ(⌜ω⌝ₛ,⌜κ⌝ₛ,⌜L⌝ₛ,X,⌜F⌝ₛ)⟫
derive_free_closed it_native_quality_m

def it_native_quality0_m : Formula 1 4 :=
  it_native_quality_m (.bound 3) (.bound 2) (.bound 1) .newest
theorem it_native_quality0_closed_l : it_native_quality0_m.FreeClosed := by
  simp -implicitDefEqProofs [it_native_quality0_m]

theorem it_native_quality_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (it_native_quality_m ω κ L F) ↔
      ∃ δ X K R, V_d (kp_pair_l hKP) δ X ∧ M.IsLimitOrdinal δ ∧
        Ep_source_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) K X R ∧
        It_local_d (kp_pair_l hKP) (ω.eval ρ) X R (κ.eval ρ) (L.eval ρ) (F.eval ρ) ∧
        Sc_inaccessible_d (ω.eval ρ) X (L.eval ρ) ∧
        Ex_strength_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) (L.eval ρ) X (F.eval ρ) := by
  simp only [it_native_quality_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    v_sigma_sat_l hKP,Formula.satisfies_isLimitOrdinal_iff,ep_source_sat_l hKP,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  apply exists_congr; intro δ
  apply exists_congr; intro X
  apply exists_congr; intro K
  apply exists_congr; intro R
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro source
  simpa only [Definitional.Term.eval_weaken,Definitional.Term.eval_newest,
    Term.eval_bound_two_push,Term.eval_bound_one_push,Term.eval_bound_zero_push] using
    ex_quality_sat_l hKP ((((ρ.push δ).push X).push K).push R)
      ω.weaken.weaken.weaken.weaken κ.weaken.weaken.weaken.weaken
      L.weaken.weaken.weaken.weaken Term.newest.weaken.weaken F.weaken.weaken.weaken.weaken
      (by simpa only [Definitional.Term.eval_weaken,Definitional.Term.eval_newest] using source)

def It_owner_d (I : kpair_convention_l.Interpretation M) (Ω c κ L F : M.Domain) : Prop :=
  ∃ X R, Smdl_d I c X R ∧ ∃ w z, Rr_layer_d I Ω X R w z ∧
    Rr_truth_d I X R it_native_quality0_m (Fin.cases F (Fin.cases L (Fin.cases κ (fun _ => w))))

def it_owner_m {d} (Ω c κ L F : Term d) : Formula 1 d := set[d] ⟪
  ∃ X R w z, ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ,X,R) ∧
    ⌜rr_layer_m⌝ₚ(⌜Ω⌝ₛ,X,R,w,z) ∧
    ⌜fun X R F L κ w => rr_truth_m (𝒞 := kpair_convention_l) it_native_quality0_m X R
      (Fin.cases F (Fin.cases L (Fin.cases κ (fun _ => w))))⌝ₚ(X,R,⌜F⌝ₛ,⌜L⌝ₛ,⌜κ⌝ₛ,w)⟫

@[simp] theorem it_owner_closed_l {d} (Ω c κ L F : Term d)
    (hΩ : Ω.freeSupport = []) (hc : c.freeSupport = []) (hκ : κ.freeSupport = [])
    (hL : L.freeSupport = []) (hF : F.freeSupport = []) : (it_owner_m Ω c κ L F).FreeClosed := by
  simp -implicitDefEqProofs [it_owner_m,Definitional.Formula.FreeClosed,hΩ,hc]
  apply rr_truth_closed_l _ it_native_quality0_closed_l _ _ _ rfl rfl
  simp -implicitDefEqProofs [Fin.forall_fin_succ,hF,hL,hκ]

theorem it_owner_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (Ω c κ L F : Term d) :
    Formula.satisfies ρ (it_owner_m Ω c κ L F) ↔
      It_owner_d I (Ω.eval ρ) (c.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [it_owner_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    smdl_sat_l I,rr_layer_sat_l I hE,
    rr_truth_sat_l I _ it_native_quality0_m it_native_quality0_closed_l,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest,tt_eval_cases_l]
  change (∃ X R w z, Smdl_d I (c.eval ρ) X R ∧
    Rr_layer_d I (Ω.eval ρ) X R w z ∧
    Rr_truth_d I X R it_native_quality0_m
      (Fin.cases (F.eval ρ) (Fin.cases (L.eval ρ) (Fin.cases (κ.eval ρ) (fun _ => w))))) ↔ _
  dsimp only [It_owner_d]
  exact ⟨fun ⟨X,R,w,z,m,n,q⟩ => ⟨X,R,m,w,z,n,q⟩,
    fun ⟨X,R,m,w,z,n,q⟩ => ⟨X,R,w,z,m,n,q⟩⟩

variable (I : kpair_convention_l.Interpretation M)

theorem it_owner_l {Ω c X R z : M.Domain} (model : Smdl_d I c X R)
    (hN : (smdl_structure_l I (R := R) model.2.1).Models KP)
    (w κ L F δ V K S : (smdl_structure_l I (R := R) model.2.1).Domain)
    (numbers : Rr_layer_d I Ω X R w.val z)
    (rank : V_d (kp_pair_l hN) δ V)
    (height : (smdl_structure_l I (R := R) model.2.1).IsLimitOrdinal δ)
    (source : Ep_source_d (kp_pair_l hN) w κ K V S)
    (loc : It_local_d (kp_pair_l hN) w V S κ L F)
    (card : Sc_inaccessible_d w V L) (strong : Ex_strength_d (kp_pair_l hN) w κ L V F) :
    It_owner_d I Ω c κ.val L.val F.val := by
  let ρ : Env (smdl_structure_l I (R := R) model.2.1) 4 :=
    ⟨Fin.cases F (Fin.cases L (Fin.cases κ (fun _ => w))),fun _ => w⟩
  have proof : Formula.satisfies ρ it_native_quality0_m :=
    (it_native_quality_sat_l hN ρ _ _ _ _).mpr ⟨δ,V,K,S,rank,height,source,loc,card,strong⟩
  have raw := (rr_truth_native_l I model.2.1 it_native_quality0_m it_native_quality0_closed_l ρ.bound).mpr
      ((Formula.closed_env_l _ it_native_quality0_closed_l (ρ := ρ)
        (η := ⟨ρ.bound,fun _ => ρ.bound 0⟩) rfl).mp proof)
  have eq : (fun i => (ρ.bound i).val) = Fin.cases F.val (Fin.cases L.val (Fin.cases κ.val (fun _ => w.val))) := by
    funext i; exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) i
  exact ⟨X,R,model,w.val,z,numbers,eq ▸ raw⟩

def It_owned_d (Ω Q E : M.Domain) : Prop :=
  ∀ i p κ L F, Rd_entry_d i p E → It_payload_d p κ L F →
    ∃ c, Rd_entry_d i c Q ∧ It_owner_d I Ω c κ L F

def it_owned_m {d} (Ω Q E : Term d) : Formula 1 d := set[d] ⟪
  ∀ i p κ L F, ⌜rd_entry0_m⌝ₚ(i,p,⌜E⌝ₛ) → ⌜it_payload_m⌝ₚ(p,κ,L,F) →
    ∃ c, ⌜rd_entry0_m⌝ₚ(i,c,⌜Q⌝ₛ) ∧ ⌜it_owner_m⌝ₚ(⌜Ω⌝ₛ,c,κ,L,F)⟫
derive_free_closed it_owned_m

theorem it_owned_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Ω Q E : Term d) :
    Formula.satisfies ρ (it_owned_m Ω Q E) ↔ It_owned_d I (Ω.eval ρ) (Q.eval ρ) (E.eval ρ) := by
  simp only [it_owned_m,It_owned_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,rd_entry0_sat_l hE,
    it_payload_sat_l hE,it_owner_sat_l I hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

theorem It_extension_d.owned_l {Ω α ξ k T Q G E β U Q' G' E' : M.Domain}
    (extension : It_extension_d α ξ k T Q G E β U Q' G' E')
    (old : It_owned_d I Ω Q E)
    (last : ∀ p κ L F, Rd_entry_d ξ p E' → It_payload_d p κ L F →
      ∃ c, Rd_entry_d ξ c Q' ∧ It_owner_d I Ω c κ L F) : It_owned_d I Ω Q' E' := by
  intro i p κ L F hp payload
  by_cases eq : i = ξ
  · exact eq ▸ last p κ L F (eq ▸ hp) payload
  · obtain ⟨c,hc,quality⟩ := old i p κ L F ((extension.2.2.2.2.2 i p eq).mp hp) payload
    exact ⟨c,extension.2.2.1 i c hc,quality⟩

theorem It_extension_d.owned_pad_l {Ω α ξ k T Q G E β U Q' G' E' : M.Domain}
    (extension : It_extension_d α ξ k T Q G E β U Q' G' E')
    (old : It_owned_d I Ω Q E)
    (empty : ∀ p, Rd_entry_d ξ p E' → ∀ x, ¬ M.mem x p) : It_owned_d I Ω Q' E' :=
  extension.owned_l I old (by
    rintro p κ L F hp ⟨r,⟨a,b,_,_,pair⟩,_⟩
    exact (empty p hp a ((pair a).mpr (Or.inl rfl))).elim)

theorem It_extension_d.owned_apply_l {Ω α ξ k T Q G E β U Q' G' E' c p κ L F : M.Domain}
    (extension : It_extension_d α ξ k T Q G E β U Q' G' E')
    (old : It_owned_d I Ω Q E)
    (unique : ∀ i x y, Rd_entry_d i x E' → Rd_entry_d i y E' → x = y)
    (move : Rd_entry_d ξ p E') (payload : It_payload_d p κ L F)
    (node : Rd_entry_d ξ c Q') (quality : It_owner_d I Ω c κ L F) : It_owned_d I Ω Q' E' :=
  extension.owned_l I old (by
    intro q μ ℓ G hq pay
    have eq := unique ξ q p hq move
    subst q
    obtain ⟨rfl,rfl,rfl⟩ := payload.unique_l pay
    exact ⟨c,node,quality⟩)

end YesMetaZFC.SetTheory.LargeCardinal
