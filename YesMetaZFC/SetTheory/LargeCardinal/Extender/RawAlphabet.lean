import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawPresent
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawApplication
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CriticalBound
import YesMetaZFC.SetTheory.LargeCardinal.Game.Basis
import YesMetaZFC.Model.SetTheory.Relations.OmegaEvaluation
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.Model.SetTheory.Relations.LayerComposition
import YesMetaZFC.SetTheory.CumulativeComparison

/-! # 原生单步的完整输出

同一次原系统、极限、共同秩段与完整代表池合在一个命题中。
整池值域、完整前驱、常值图方块及相对公式真值一并保留。
反射证书的读取直接返回此结论，后继与复制消费者使用同一份实际见证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 固定到本次实际极限及其图的完整证书，供同步复制保留同一后继。 -/
def Er_rank_cut_at_d (ω c X R c' Y S q Γ k N S₀ z c₁ : M.Domain)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := S₀) nx).Models KP)
    (U₀ w ξ ℓ e β X' K' jN : (smdl_structure_l I (R := S₀) nx).Domain)
    (L J O Z A p T V r o C W j q' p₀ : M.Domain) : Prop :=
  Fs_read_d (M := smdl_structure_l I (R := S₀) nx) w U₀ ∧
  Rr_closed_d I N S₀ U₀.val ∧
  (∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U₀.val S₀) ∧
  (smdl_structure_l I (R := S₀) nx).mem β U₀ ∧
  (smdl_structure_l I (R := S₀) nx).mem β X' ∧
  (smdl_structure_l I (R := S₀) nx).TransitiveSet β ∧
  (∀ m d : (smdl_structure_l I (R := S₀) nx).Domain,
    (smdl_structure_l I (R := S₀) nx).mem m w →
    Ep_space_d (M := smdl_structure_l I (R := S₀) nx) ξ m d →
    ∃ P : (smdl_structure_l I (R := S₀) nx).Domain, (smdl_structure_l I (R := S₀) nx).mem P U₀ ∧
      (smdl_structure_l I (R := S₀) nx).IsCartesianProduct (kp_pair_l hN) P d β) ∧
    (∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val S₀) ∧
    Er_graph_d I ω L N S₀ ξ.val ℓ.val e.val z Y S k J O Z A p T V ∧
    Di_system_d J O A p T V ∧ Di_limit_d A p T V r C W ∧ Smdl_d I o C W ∧ Sc_theory_d I ω C W ∧ Sc_collection_d I ω C W ∧
    Di_elementary_d I ω O A p T V ∧ Smap_d I ω c' o Y C j ∧ Smap_d I ω c o X C q' ∧
    Er_constants_d Y r j ∧ Er_agree_d I ω N S₀ ξ.val z Γ Y S k ∧ It_payload_d p₀ ξ.val ℓ.val e.val ∧ It_active_d hZF ω c₁ c' o j p₀ ∧
    (Zc_model_d I ω c X R → Zc_model_d I ω o C W) ∧
    (∀ x E, Rd_entry_d x E q' ↔ M.mem x X ∧ ∃ y, Rd_entry_d x y q ∧ Rd_entry_d y E j) ∧
  ∃ U : (smdl_structure_l I (R := S₀) nx).Domain,
    V_d (kp_pair_l hN) ℓ U ∧ Fs_read_d w U ∧
    (∃ cU R_U, Smem_d (kp_pair_l hN) cU U R_U ∧
      Sc_theory_d (kp_pair_l hN) w U R_U) ∧
    Rr_small_d I N S₀ U.val ∧
    ∃ l H₂ D u, Ic_common_d I N S₀ C W ℓ.val l U.val H₂ D u ∧ Rr_small_d I C W H₂ ∧
      (∀ x y : (smdl_structure_l I (R := S₀) nx).Domain, ∀ b E,
        (smdl_structure_l I (R := S₀) nx).mem x β → (smdl_structure_l I (R := S₀) nx).mem y U →
        Rd_entry_d x y jN → Rd_entry_d x.val b k → (Rd_entry_d y.val E u ↔ Rd_entry_d b E j)) ∧
      ∃ P : (smdl_structure_l I (R := S₀) nx).Domain,
        V_d (kp_pair_l hN) ξ P ∧
        (∀ x : (smdl_structure_l I (R := S₀) nx).Domain, ∀ b E,
          (smdl_structure_l I (R := S₀) nx).mem x P → Rd_entry_d x.val b k →
            (Rd_entry_d x.val E u ↔ Rd_entry_d b E j)) ∧
      ∃ κ₀ bκ κ', Rd_entry_d ξ.val κ₀ u ∧ Rd_entry_d ξ.val bκ k ∧ Rd_entry_d bκ κ' j ∧
        Rd_entry_d κ₀ l W ∧ (∀ E, Rd_entry_d E l W → Rd_entry_d E κ' W) ∧ κ₀ ≠ κ' ∧
        Rd_entry_d κ₀ κ' W ∧
        Rr_truth_d I Y S (KP.ord0_m .newest) (fun _ : Fin 1 => bκ) ∧
        Rr_truth_d I C W (KP.ord0_m .newest) (fun _ : Fin 1 => κ₀) ∧
        Rr_truth_d I C W (KP.ord0_m .newest) (fun _ : Fin 1 => κ') ∧
        (∀ x b E, M.mem x N → Rd_entry_d x ξ.val S₀ → Rd_entry_d x b k →
          (Rd_entry_d x E u ↔ Rd_entry_d b E j)) ∧
        (∀ γ, It_lower_d I γ N S₀ ξ.val →
          It_lower_d I γ Y S bκ ∧ It_lower_d I γ C W κ₀ ∧
          ∃ h₀ h₁ z₀ z₁, Rr_layer_d I γ Y S h₀ z₀ ∧ Rr_layer_d I γ C W h₁ z₁ ∧
            ∀ x b, Rd_entry_d x b z₀ → ∀ E, Rd_entry_d x E z₁ ↔ Rd_entry_d b E j) ∧
        (∀ γ B a V s t, Rr_layer_d I γ N S₀ a s → Rr_layer_d I B N S₀ V t →
          Rr_rank_d I N S₀ a V → (∀ x, Rd_entry_d x a S₀ → Rd_entry_d x ξ.val S₀) →
          Tg_anchor_d I γ B Y S q → Tg_anchor_d I γ B C W q') ∧
      ∃ cD R_D, ∃ cut : Smdl_d I cD D R_D,
        (∀ x y, Rd_entry_d x y R_D ↔ M.mem x D ∧ M.mem y D ∧ Rd_entry_d x y S₀) ∧
        Rf_ext_d I D R_D ∧
        (∀ η : Env (smdl_structure_l I (R := R_D) cut.2.1) 0,
          Formula.satisfies η (.conj sc_algebra_m sc_power_m)) ∧
        Rr_truth_d I D R_D (fs_read0_m .newest) (fun _ : Fin 1 => w.val) ∧
        (smdl_structure_l I (R := R_D) cut.2.1).Models ZFC ∧
        (∀ E F n r i f B, M.IsFunctionSpace I E ω D → Sfm_d I ω n F → M.mem r n →
          M.mem i ω → M.mem f E → M.mem B D → ∃ A, M.mem A D ∧ Sr_sep_d I D R_D E F n r i f B A) ∧
        ∃ s, Rr_layer_d I ω D R_D w.val s ∧
          (∀ n a, M.mem n ω → Fn0_d n D a →
            ∃ m f, Rd_entry_d n m s ∧ Rf_fun_d I D R_D m f ∧ Rc_graph_d I D R_D s f a) ∧
        (Sc_bounded_omega_closed_d I ω N S₀ → Sc_omega_closed_d I ω D R_D) ∧
        ∃ w₀ w₁ z₀ z₁, Rd_entry_d w.val w₀ k ∧ Rd_entry_d w.val w₁ u ∧ Rd_entry_d w₀ w₁ j ∧
          Rr_layer_d I ω Y S w₀ z₀ ∧ Rr_layer_d I ω C W w₁ z₁ ∧
          (∀ n x, Rd_entry_d n x z₀ ↔ ∃ m, Rd_entry_d n m z ∧ Rd_entry_d m x k) ∧
          (∀ n x, Rd_entry_d n x z₁ ↔ ∃ m, Rd_entry_d n m z ∧ Rd_entry_d m x u) ∧
          (∀ n x, Rd_entry_d n x z₀ → ∀ y, Rd_entry_d n y z₁ ↔ Rd_entry_d x y j) ∧
          (∀ v t, Rr_layer_d I ω X R v t → Sc_sequences_d I v X R →
            Rd_entry_d v w₀ q ∧ Rd_entry_d v w₁ q' ∧
            Sc_sequences_d I w₀ Y S ∧ Sc_sequences_d I w₁ C W) ∧
          (Sc_bounded_omega_closed_d I ω N S₀ → ∀ f, Fn0_d ω C f →
            (∀ n E, Rd_entry_d n E f → Rd_entry_d E H₂ W) →
              ∃ F, Rd_entry_d F H₂ W ∧ Rf_fun_d I C W w₁ F ∧ Rc_graph_d I C W z₁ F f) ∧
          (∀ a₀, M.mem a₀ J → ∃ n, ∃ m b₀ d₀ : (smdl_structure_l I (R := S₀) nx).Domain, ∃ D₀ t₀ y₀ a₁,
            M.mem n ω ∧ Rd_entry_d n m.val z ∧ Rr_finite_d I ω L N S₀ z a₀ b₀.val ∧
            Fn0_d m ℓ b₀ ∧ Ep_space_d ξ m d₀ ∧
            (∀ s, M.mem s D₀ ↔ M.mem s N ∧ Rd_entry_d s d₀.val S₀) ∧
            Fn0_d D₀ Y t₀ ∧ M.IsRestrictionOf I t₀ k D₀ ∧ Rd_entry_d d₀.val y₀ k ∧ Ep_repr_d r a₀ t₀ a₁ ∧ Rd_entry_d b₀.val a₁ u ∧
            (∀ f g E F, Rf_fun_d I Y S y₀ f → Rc_graph_d I Y S t₀ f g →
              Ep_repr_d r a₀ g E → Rd_entry_d f F j → Rf_val_d I C W a₁ E F) ∧
            Er_seed_d I ω L N S₀ ξ.val e.val z Y S k r a₀ a₁ ∧
            (∀ b f x : (smdl_structure_l I (R := S₀) nx).Domain, ∀ b' f' E F,
              Fn0_d d₀ b f → KPair_d (smdl_structure_l I (R := S₀) nx) x b₀ f →
              Rd_entry_d b.val b' k → Rd_entry_d f.val f' k →
              Er_eval_d I ω L N S₀ z Γ Y k r x.val E → Rd_entry_d f' F j → Rf_val_d I C W a₁ E F)) ∧
          (∀ E, M.mem E C → ∃ b d f a F, M.mem b D ∧ Rf_fun_d I Y S d f ∧
            Rd_entry_d b a u ∧ Rd_entry_d f F j ∧ Rf_val_d I C W a E F) ∧
          (Sc_omega_closed_d I ω Y S → Sc_bounded_omega_closed_d I ω N S₀ → Sc_omega_closed_d I ω C W) ∧
          (Sc_collapse_d I X R → Sc_collapse_d I C W) ∧
          (∀ n a, M.mem n ω → Fn0_d n C a → ∃ m f, Rd_entry_d n m z₁ ∧
            Rf_fun_d I C W m f ∧ Rc_graph_d I C W z₁ f a) ∧
          (∀ v t, Rr_layer_d I ω X R v t → Sc_sequences_d I v X R →
            ∀ A, M.mem A C → ∃ B A₀ K₀ B₀ p₀,
            Sc_fseq_d I w₁ A B C W ∧
            (∀ x, M.mem x A₀ ↔ M.mem x C ∧ Rd_entry_d x A W) ∧ Fseq_space_d I ω A₀ K₀ ∧
            (∀ f, M.mem f B₀ ↔ M.mem f C ∧ Rd_entry_d f B W) ∧ M.IsSetBijectionFromTo I p₀ K₀ B₀ ∧
            ∀ g f, Rd_entry_d g f p₀ ↔ Rr_finite_d I ω A₀ C W z₁ g f) ∧
          (∃ A₁ Q₁ Y₁ e₁ : (smdl_structure_l I (R := S₀) nx).Domain, ∃ D₁ B₁ s₁ v₁ t₁,
            Eb_collapse_d w ξ ℓ K' X' β e A₁ Q₁ Y₁ e₁ ∧
            (∀ x, M.mem x D₁ ↔ M.mem x N ∧ Rd_entry_d x A₁.val S₀) ∧
            (∀ x, M.mem x B₁ ↔ M.mem x N ∧ Rd_entry_d x Y₁.val S₀) ∧ Fn0_d D₁ B₁ s₁ ∧
            (∀ a b : (smdl_structure_l I (R := S₀) nx).Domain, Rd_entry_d a.val b.val s₁ ↔ Rd_entry_d a b e₁) ∧
            Fn0_d D₁ C v₁ ∧
            (∀ a E, Rd_entry_d a E v₁ ↔ M.mem a D₁ ∧ Er_eval_d I ω L N S₀ z Γ Y k r a E) ∧
            M.IsSetInjectionFromTo I t₁ B₁ C ∧ M.IsRestrictionOf I u t₁ D ∧
            Rd_entry_d ℓ.val l t₁ ∧ Rd_entry_d U.val H₂ t₁ ∧
            Er_present_d I ω L N S₀ z Γ Y k r e₁.val D₁ t₁ ∧
            (∀ a : (smdl_structure_l I (R := S₀) nx).Domain, (smdl_structure_l I (R := S₀) nx).mem a A₁ →
              ∃ α, ∃ m b d f : (smdl_structure_l I (R := S₀) nx).Domain,
                Ei_d ω L α ∧ Rr_finite_d I ω L N S₀ z α b.val ∧
                (smdl_structure_l I (R := S₀) nx).mem m w ∧ Fn0_d m ℓ b ∧ Ep_space_d ξ m d ∧
                (smdl_structure_l I (R := S₀) nx).mem f U₀ ∧ Fn0_d d β f ∧
                KPair_d (smdl_structure_l I (R := S₀) nx) a b f) ∧
            ∃ bβ Hβ, Rd_entry_d β.val bβ k ∧ Rd_entry_d bβ Hβ j ∧
              (∀ E, Rd_entry_d E Hβ W ↔ ∃ x, M.mem x B₁ ∧ Rd_entry_d x E t₁) ∧
              (∀ x E, Rd_entry_d x E t₁ → ∀ P,
                Rd_entry_d P E W ↔ ∃ y, Rd_entry_d y x S₀ ∧ Rd_entry_d y P t₁) ∧
              (∀ x y : (smdl_structure_l I (R := S₀) nx).Domain, ∀ b E,
                (smdl_structure_l I (R := S₀) nx).mem x β → Rd_entry_d x y jN →
                Rd_entry_d x.val b k → (Rd_entry_d y.val E t₁ ↔ Rd_entry_d b E j)) ∧
              ∀ {s}, ∀ φ : Formula 1 s, φ.FreeClosed → ∀ v w : Fin s → M.Domain,
                (∀ i, Rd_entry_d (v i) (w i) t₁) →
                (Rr_truth_d I N S₀ (lr_rel_m φ .newest (fun i => .bound i.succ)) (Fin.cases Y₁.val v) ↔
                  Rr_truth_d I C W (lr_rel_m φ .newest (fun i => .bound i.succ)) (Fin.cases Hβ w))) ∧
          (let out : Prop :=
            ∃ K, Er_source_d I ω w₁ w₁ K C W ∧ It_source_d hZF ω o ∧
              ∀ α i T₀ Q₀ G₀ E₀ k₀ o₀, It_tree_d hZF ω c α T₀ Q₀ G₀ E₀ →
                M.SuccessorOf α i → Rd_entry_d i c₁ Q₀ → Rd_entry_d k₀ c' Q₀ → It_map_d G₀ o₀ k₀ q →
                ∃ β T₁ Q₁ G₁ E₁, It_tree_d hZF ω c β T₁ Q₁ G₁ E₁ ∧
                  It_extension_d α i k₀ T₀ Q₀ G₀ E₀ β T₁ Q₁ G₁ E₁ ∧
                  Rd_entry_d α o Q₁ ∧ It_map_d G₁ k₀ α j ∧ Rd_entry_d i p₀ E₁ ∧ It_map_d G₁ o₀ α q' ∧
                  ∀ γ, It_lower_d I γ N S₀ ξ.val → It_critical_bound_d I γ Q₀ E₀ →
                    It_critical_bound_d I γ Q₁ E₁;
            (∀ v t, Rr_layer_d I ω X R v t → Sc_sequences_d I v X R → Sc_collapse_d I X R → out) ∧
            (Zc_model_d I ω c X R → out))

def Er_rank_cut_d (ω c X R c' Y S q Γ k N S₀ z c₁ : M.Domain)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := S₀) nx).Models KP)
    (U₀ w ξ ℓ e β X' K' jN : (smdl_structure_l I (R := S₀) nx).Domain) : Prop :=
  ∃ L J O Z A p T V r o C W j q' p₀,
    Er_rank_cut_at_d hZF ω c X R c' Y S q Γ k N S₀ z c₁ nx hN U₀ w ξ ℓ e β X' K' jN
      L J O Z A p T V r o C W j q' p₀

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原生一步施加的字母满像与有限前缀

同一次工厂已经给出 Vκ 上的常值方块及完整共同前驱。原字母表属于
这个原生秩段时，每个新字母必有唯一旧原像；整个论证不要求字母码
或所属模型在背景中传递。实际限制图继而搬运全部内部有限前缀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

variable {ω c X R c' Y S q Γ k N S₀ z c₁ : M.Domain}
  {nx : ∃ x, M.mem x N}
  {hN : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := S₀) nx).Models KP}
  {U₀ w ξ ℓ e β X' K' jN : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := S₀) nx).Domain}
  {L J O Z A p T V r o C W j q' p₀ : M.Domain}
  (data : Er_rank_cut_at_d hZF ω c X R c' Y S q Γ k N S₀ z c₁ nx hN U₀ w ξ ℓ e β X' K' jN
    L J O Z A p T V r o C W j q' p₀)
include data

/-- 原生 rank(A)<κ 通过实际 Vα 证书读取，同一原超幂不增加字母。 -/
theorem Er_rank_cut_at_d.alphabet_image_l
    (α B a : (smdl_structure_l I (R := S₀) nx).Domain) {b b' : M.Domain}
    (rank : V_d (kp_pair_l hN) α B)
    (member : (smdl_structure_l I (R := S₀) nx).mem a B)
    (below : (smdl_structure_l I (R := S₀) nx).MemberSubset α ξ)
    (image : Rd_entry_d a.val b k) (next : Rd_entry_d b b' j) :
    ∀ E, Rd_entry_d E b' W ↔ ∃ x, Rd_entry_d x b S ∧ Rd_entry_d x E j := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,agreement,_,_,_,_,
    U,_,_,_,_,l,H,D,u,common,_,_,P,rankP,keep,_⟩ := data
  have ha := (KP.v_compare_l hN rank rankP below).1 a member
  have hA := (keep a b b' ha image).mpr next
  intro E
  constructor
  · intro hE
    obtain ⟨x,hxa,hxE⟩ := (common.pred a.val b' hA E).mp hE
    have hx := ((common.carrier x).mp (common.injection.1.input_mem_of_pairMember hxE)).1
    have hxΓ := agreement.downward a.val x (agreement.injection.1.input_mem_of_pairMember image) hx hxa
    obtain ⟨y,_,hxy⟩ := agreement.injection.1.2.2 x hxΓ
    have low := v_transitive_l (kp_pair_l hN) rankP a ha ⟨x,hx⟩ hxa
    exact ⟨y,(agreement.predecessors a.val b image y).mpr ⟨x,hxa,hxy⟩,
      (keep ⟨x,hx⟩ y E low hxy).mp hxE⟩
  · rintro ⟨y,hy,hyE⟩
    obtain ⟨x,hxa,hxy⟩ := (agreement.predecessors a.val b image y).mp hy
    have hx := agreement.domain x (agreement.injection.1.input_mem_of_pairMember hxy)
    have low := v_transitive_l (kp_pair_l hN) rankP a ha ⟨x,hx⟩ hxa
    exact (common.pred a.val b' hA E).mpr ⟨x,hxa,(keep ⟨x,hx⟩ y E low hxy).mpr hyE⟩

/-- 两端字母集合和同一边的限制双射由工厂实际构造，有限前缀沿它取像。 -/
theorem Er_rank_cut_at_d.alphabet_l
    (α B a : (smdl_structure_l I (R := S₀) nx).Domain) {b b' : M.Domain}
    (rank : V_d (kp_pair_l hN) α B)
    (member : (smdl_structure_l I (R := S₀) nx).mem a B)
    (below : (smdl_structure_l I (R := S₀) nx).MemberSubset α ξ)
    (image : Rd_entry_d a.val b k) (next : Rd_entry_d b b' j) :
    ∃ D E t,
      (∀ x, M.mem x D ↔ M.mem x Y ∧ Rd_entry_d x b S) ∧
      (∀ x, M.mem x E ↔ M.mem x C ∧ Rd_entry_d x b' W) ∧
      M.IsSetBijectionFromTo I t D E ∧ M.IsRestrictionOf I t j D ∧
      ∀ n f, Fn0_d n D f → ∃ f', Fn0_d n E f' ∧ Smap_assign_d I n j f f' := by
  have full := data.alphabet_image_l hZF α B a rank member below image next
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,embed,_⟩ := data
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨D,ds⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases b (fun _ => S),fun _ => Y⟩ Y
  obtain ⟨E,es⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases b' (fun _ => W),fun _ => C⟩ C
  have domain x : M.mem x D ↔ M.mem x Y ∧ Rd_entry_d x b S :=
    (ds x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  have range x : M.mem x E ↔ M.mem x C ∧ Rd_entry_d x b' W :=
    (es x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  obtain ⟨t,rest⟩ := ZF.exists_restriction hZF I j D
  have fn := fn0_of_function_l (ZF.modelsKP hZF)
    (rest.isSetFunctionFromTo embed.1.1 (fun x hx => ((domain x).mp hx).1))
  have bound x y (hxy : Rd_entry_d x y t) : M.mem y E := by
    obtain ⟨hx,hxy⟩ := (rest.2 x y).mp hxy
    exact (range y).mpr ⟨embed.1.1.output_mem_of_pairMember hxy,
      (full y).mpr ⟨x,((domain x).mp hx).2,hxy⟩⟩
  have ft := fn0_function_l (ZF.modelsKP hZF) (fn.retarget_l bound)
  have bij : M.IsSetBijectionFromTo I t D E := by
    refine ⟨⟨ft,fun x y z hx hy => embed.1.2 x y z
      ((rest.2 x z).mp hx).2 ((rest.2 y z).mp hy).2⟩,?_⟩
    intro y hy
    obtain ⟨x,hx,hxy⟩ := (full y).mp ((range y).mp hy).2
    have hxD := (domain x).mpr ⟨embed.1.1.input_mem_of_pairMember hxy,hx⟩
    exact ⟨x,hxD,(rest.2 x y).mpr ⟨hxD,hxy⟩⟩
  refine ⟨D,E,t,domain,range,bij,rest,?_⟩
  intro n f ff
  obtain ⟨f',fg,graph⟩ := ZF.exists_compositionFunction hZF I (fn0_function_l (ZF.modelsKP hZF) ff) ft
  refine ⟨f',fn0_of_function_l (ZF.modelsKP hZF) fg,?_⟩
  intro i hi x y hix hxy
  exact (graph i y).mpr ⟨hi,x,hix,(rest.2 x y).mpr ⟨(ff.bound_l hix).2,hxy⟩⟩

/-- 工厂自身的两份数字图把同一字母双射接到原生有限函数码。 -/
theorem Er_rank_cut_at_d.alphabet_codes_l
    (hw : M.IsOmega ω) (parent : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (α B a : (smdl_structure_l I (R := S₀) nx).Domain) {b b' : M.Domain}
    (rank : V_d (kp_pair_l hN) α B)
    (member : (smdl_structure_l I (R := S₀) nx).mem a B)
    (below : (smdl_structure_l I (R := S₀) nx).MemberSubset α ξ)
    (image : Rd_entry_d a.val b k) (next : Rd_entry_d b b' j) :
    ∃ D E t w₀ w₁ z₀ z₁,
      (∀ x, M.mem x D ↔ M.mem x Y ∧ Rd_entry_d x b S) ∧
      (∀ x, M.mem x E ↔ M.mem x C ∧ Rd_entry_d x b' W) ∧
      M.IsSetBijectionFromTo I t D E ∧ M.IsRestrictionOf I t j D ∧
      Rr_layer_d I ω Y S w₀ z₀ ∧ Rr_layer_d I ω C W w₁ z₁ ∧
      ∀ n f F, Fn0_d n D f → Rr_finite_d I ω D Y S z₀ f F →
        ∃ f' F', Fn0_d n E f' ∧ Smap_assign_d I n j f f' ∧ Rd_entry_d F F' j ∧
          Rr_finite_d I ω E C W z₁ f' F' := by
  obtain ⟨D,E,t,domain,range,bij,rest,lift⟩ :=
    data.alphabet_l hZF α B a rank member below image next
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,target,_,_,_,embed,_,_,_,_,_,_,_,tail⟩ := data
  obtain ⟨U,_,_,_,_,l,H,D₀,u,_,_,_,P,_,_,κ₀,bκ,κ',_,_,_,_,_,_,_,_,_,_,_,_,_,tail⟩ := tail
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,tail⟩ := tail
  obtain ⟨w₀,w₁,z₀,z₁,_,_,_,source,numbers,_⟩ := tail
  refine ⟨D,E,t,w₀,w₁,z₀,z₁,domain,range,bij,rest,source,numbers,?_⟩
  intro n f F fn code
  obtain ⟨f',fn',assign⟩ := lift n f fn
  have memberF := code.elim fun _ h => h.elim fun _ h => h.2.2.2.1.mem_l I
  obtain ⟨F',_,iF⟩ := embed.1.1.2.2 F memberF
  exact ⟨f',F',fn',assign,iF,code.image_l hZF hw parent target embed ext source numbers fn fn' assign iF⟩

end YesMetaZFC.SetTheory.LargeCardinal
