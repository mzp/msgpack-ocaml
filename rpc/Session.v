Add LoadPath "../applpi".
Add LoadPath "../proof".

Require Import List String.
Require Import libapplpi.
Require Import Object MultiByte.

Record request : Set := Request {
  request_id : ascii32;
  method : string;
  params : list object
}.

Record response : Set := Response {
  response_id : ascii32;
  error  : object;
  result : object
}.

Record notice : Set := Notice {
  notice_method : string;
  notice_params : list object
}.

Inductive session : Set :=
|  Call   (_ : request) (_ : chan response true)
|  Notify (_ : notice).