import YesMetaZFC.Model.Forcing.Order.QueryAttempt
import YesMetaZFC.Model.Forcing.Order.GenericHullCollapse
import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism

/-! # 有限名字检查在同一坍塌泛型中恢复完整实数图

根位置确定唯一的原名字及检查基准。每条数字检查沿返回初等图反射到
实际传递模型，被同一泛型接受；函数的全定义性排除额外图边。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem nr_value_l {c X R N d H B π j cB RB P' V' G e f x u v w : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : Extensional (smdl_structure_l I (R := R) source.1.2.1))
    (ω P V : (smdl_structure_l I (R := R) source.1.2.1).Domain) (hw : M.IsOmega ω.val)
    (h : Gh_collapse_d hZF ω.val c X N d P.val V.val H B π j cB RB P' V' G)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P V P)
    (fe : Fn0_d ω.val N e) (ff : Fn0_d ω.val N f) (fx : Fn0_d ω.val ω.val x)
    (fu : Fn0_d ω.val ω.val u) (fv : Fn0_d ω.val ω.val v) (fw : Fn0_d ω.val ω.val w)
    (accepted : ∀ i p, Rd_entry_d i p f → M.mem p H) (run : Nr_at_d ω.val X P.val V.val ω.val e f x u v w) :
    let C := smdl_structure_l I (R := RB) h.model.1.2.1
    let hC := ZFC.models_zf_l (h.theory.native_l I hZF hw)
    let p : C.Domain := ⟨P',(h.collapse.function.bound_l h.conditions).2⟩
    let t : C.Domain := ⟨V',(h.collapse.function.bound_l h.order).2⟩
    ∃ o a c b τ p₀, (∀ z, ¬ M.mem z o) ∧ Rd_entry_d o a v ∧ Rd_entry_d o c w ∧
      Rd_entry_d a b e ∧ Rd_entry_d c τ e ∧ Rd_entry_d o p₀ f ∧ Fn_bg_d B P' V' P' ω.val ω.val G x ∧
      ∃ hwB : M.mem ω.val B, ∃ τ' : C.Domain, Rd_entry_d τ τ'.val π ∧
        Fn_value_d hC Subtype.val p t p ⟨ω.val,hwB⟩ τ' (fun p => M.mem p.val G) x ∧
        ∃ b' p' : C.Domain, Rd_entry_d b b'.val π ∧ Rd_entry_d p₀ p'.val π ∧ M.mem b'.val G ∧ M.mem p'.val G := by
  let L := smdl_structure_l I (R := R) source.1.2.1
  let C := smdl_structure_l I (R := RB) h.model.1.2.1
  have small := ZFC.models_zf_l (h.theory.native_l I hZF hw)
  obtain ⟨hwB,_,_,_⟩ := h.numbers_l hZF hw source trans
  let Ω : C.Domain := ⟨ω.val,hwB⟩
  let P₁ : C.Domain := ⟨P',(h.collapse.function.bound_l h.conditions).2⟩
  let V₁ : C.Domain := ⟨V',(h.collapse.function.bound_l h.order).2⟩
  obtain ⟨o,empty,ho⟩ := hw.1.1
  obtain ⟨a,ha,oa⟩ := fv.2.1 o ho
  obtain ⟨c,hc,oc⟩ := fw.2.1 o ho
  obtain ⟨b,hb,ab⟩ := fe.2.1 a ha
  obtain ⟨τ,hτ,cτ⟩ := fe.2.1 c hc
  obtain ⟨p₀,hp,op⟩ := ff.2.1 o ho
  obtain ⟨bP,pb,base⟩ := run.root o a c p₀ b τ ho ha hc empty oa oc ab cτ op
  obtain ⟨b',hb',bb⟩ := h.collapse.function.2.1 b hb
  obtain ⟨τ',hτ',ττ⟩ := h.collapse.function.2.1 τ hτ
  obtain ⟨p',hp',pp⟩ := h.collapse.function.2.1 p₀ hp
  let b₁ : C.Domain := ⟨b',hb'⟩
  let τ₁ : C.Domain := ⟨τ',hτ'⟩
  let p₁ : C.Domain := ⟨p',hp'⟩
  obtain ⟨g,elem,values⟩ := h.embedding.project_l I hZF hw h.model.1 source.1
  have point (z : C.Domain) (y : M.Domain) (yz : Rd_entry_d y z.val π) : (g z).val = y :=
    h.embedding.1.1.1.2 _ _ _ (values z) ((h.inverse_entries y z.val).mpr yz)
  have gP : g P₁ = P := Subtype.ext (point P₁ P.val h.conditions)
  have gV : g V₁ = V := Subtype.ext (point V₁ V.val h.order)
  have gΩ : g Ω = ω := Subtype.ext (h.embedding.1.1.1.2 _ _ _ (values Ω)
    (h.embedding.omega_l I hZF hw h.transitive trans h.model source hwB))
  have gb := point b₁ b bb
  have gτ := point τ₁ τ ττ
  have gp := point p₁ p₀ pp
  have fixed (z : C.Domain) (hz : M.mem z.val ω.val) : (g z).val = z.val :=
    h.embedding.1.1.1.2 _ _ _ (values z) (h.embedding.natural_l hZF hw h.transitive trans h.model source hwB z.val hz)
  have order : Cond_order_d C P₁ V₁ P₁ := by
    let ρ : Env C 3 := ⟨fun i => [P₁,V₁,P₁].get i,fun _ => P₁⟩
    apply (cond_order_sat_l small.1 ρ (.bound 0) (.bound 1) (.bound 2)).mp
    apply (elem (cond_order_m (.bound 0) (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs) ρ).mpr
    apply (cond_order_sat_l native (image_env_l g ρ) (.bound 0) (.bound 1) (.bound 2)).mpr
    change Cond_order_d L (g P₁) (g V₁) (g P₁)
    simpa only [gP,gV] using O
  have generic := ((h.model.generic_code_l I hZF.1 h.transitive (ZF.modelsKP small) P₁ V₁ P₁ G).mp h.generic).2
  have pG : M.mem p' G := (h.accepted_l hZF pp).mp (accepted o p₀ op)
  have bG : M.mem b' G := h.generic.upward p' b' pG ((h.collapse.member b P.val b' P' bb h.conditions).mp bP)
    ((h.embedding.entry_l hZF hw h.transitive trans h.model source
      ((h.inverse_entries p₀ p').mpr pp) ((h.inverse_entries b b').mpr bb)
      ((h.inverse_entries V.val V').mpr h.order)).mpr pb)
  let ρ : Env C 6 := ⟨fun i => [P₁,V₁,Ω,b₁,τ₁,p₁].get i,fun _ => τ₁⟩
  have base₀ : Formula.satisfies (image_env_l g ρ) nr_base0_m := by
    apply (nr_base_native_l native _).mpr
    change ∃ t, Check_d L (g b₁) (g Ω) t ∧ Fn_name_d L (g P₁) (g V₁) (g P₁) (g p₁) t t (g τ₁)
    rw [gP,gV,gΩ]
    exact (nr_base_read_l I source trans native P V ω (g b₁) (g τ₁) (g p₁)).mp (by simpa only [gb,gτ,gp] using base)
  obtain ⟨t,check,typed⟩ := (nr_base_native_l small.1 ρ).mp ((elem nr_base0_m nr_base0_closed_l ρ).mpr base₀)
  obtain ⟨k,checks,full,ki⟩ := check_map_l order small generic (b := b₁) bG
  obtain ⟨y,value⟩ := name_value_l (R := V₁) (z := P₁) (U := fun p => M.mem p.val G) typed.2.2.1
  have fn := fn_name_val_l order small generic typed pG (checks Ω t check) (checks Ω t check) value
  have hE := preserves_zf_l order small generic
  have ci : Function.Injective (Subtype.val : C.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have vi i (hi : M.mem i ω.val) : Rd_entry_d i a v := by
    obtain ⟨a',_,ia⟩ := fv.2.1 i hi
    exact run.base_index i o a' a hi ho ia oa ▸ ia
  have wi i (hi : M.mem i ω.val) : Rd_entry_d i c w := by
    obtain ⟨c',_,ic⟩ := fw.2.1 i hi
    exact run.name_index i o c' c hi ho ic oc ▸ ic
  have rows (i : C.Domain) (hi : C.mem i Ω) : ∃ z, Entry_d M i.val z.val x ∧
      Entry_d (extension_l C small P₁ V₁ P₁ (fun p => M.mem p.val G)) (k i) (k z) y := by
    have hiω := (smem_member_l I h.model.1 h.model.2 i Ω).mp hi
    obtain ⟨z,hz,iz⟩ := fx.2.1 i.val hiω
    let z₁ : C.Domain := ⟨z,h.transitive ω.val hwB z hz⟩
    obtain ⟨n,hn,in'⟩ := fu.2.1 i.val hiω
    obtain ⟨q,hq,nq⟩ := ff.2.1 n hn
    have digit := run.digits i.val n a c z q b τ hiω hn ha hc iz in' nq (vi i.val hiω) (wi i.val hiω) ab cτ
    obtain ⟨q',hq',qq⟩ := h.collapse.function.2.1 q hq
    let q₁ : C.Domain := ⟨q',hq'⟩
    have gq := point q₁ q qq
    let η : Env C 8 := ⟨fun a => [P₁,V₁,P₁,b₁,τ₁,i,z₁,q₁].get a,fun _ => τ₁⟩
    have old : Formula.satisfies (image_env_l g η) nentry0_m := by
      apply (nentry_sat_l native _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)).mpr
      change Nentry_d (g P₁) (g V₁) (g P₁) (g b₁) (g τ₁) (g i) (g z₁) (g q₁)
      rw [gP,gV]
      exact (nr_edge_read_l I source trans native P V (g b₁) (g τ₁) (g i) (g z₁) (g q₁)).mp
        (by simpa only [gb,gτ,gq,fixed i hiω,fixed z₁ hz] using digit)
    have force := (nentry_sat_l small.1 η (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)).mp
      ((elem nentry0_m nentry0_closed_l η).mpr old)
    exact ⟨z₁,iz,(nentry_truth_l small order generic (b := b₁) bG value k checks i z₁).mp
      ⟨q₁,(h.accepted_l hZF qq).mp (accepted n q nq),force⟩⟩
  have read := (function_read_l (ZF.modelsKP hZF) (ZF.modelsKP hE) Subtype.val ci
    (smem_full_l I h.model h.transitive) k ki full (fn0_function_l (ZF.modelsKP hZF) fx) fn rows).1
  have result : Fn_value_d small (M := M) Subtype.val P₁ V₁ P₁ Ω τ₁ (fun p => M.mem p.val G) x :=
    ⟨k,y,value,(fun a => (gval_check_map_l order small generic (b := b₁) bG k checks a (k a)).mpr rfl),
      fn0_of_function_l (ZF.modelsKP hE) fn,read⟩
  exact ⟨o,a,c,b,τ,p₀,empty,oa,oc,ab,cτ,op,
    (fn_bg_read_l I hZF.1 h.model h.transitive small.1 P₁ V₁ P₁ Ω Ω G x).mpr (result.code_l small order generic),
    hwB,τ₁,ττ,result,b₁,p₁,bb,pp,bG,pG⟩

end YesMetaZFC.Model.Forcing.Internal
