unit GR32.ImageFormats.TClipboard;

(* ***** BEGIN LICENSE BLOCK *****
 * Version: MPL 1.1 or LGPL 2.1 with linking exception
 *
 * The contents of this file are subject to the Mozilla Public License Version
 * 1.1 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an "AS IS" basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * Alternatively, the contents of this file may be used under the terms of the
 * Free Pascal modified version of the GNU Lesser General Public License
 * Version 2.1 (the "FPC modified LGPL License"), in which case the provisions
 * of this license are applicable instead of those above.
 * Please see the file LICENSE.txt for additional information concerning this
 * license.
 *
 * The Original Code is image format support for Graphics32
 *
 * The Initial Developer of the Original Code is
 * Anders Melander <anders@melander.dk>
 *
 * Portions created by the Initial Developer are Copyright (C) 2008-2022
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *
 * ***** END LICENSE BLOCK ***** *)

// WEAKPACKAGEUNIT so we can include the unit in the GR32 design time
// package in order to have the design time editor support the various formats.
{$WEAKPACKAGEUNIT ON}

interface

{$I GR32.inc}

implementation

uses
  Classes,
  ClipBrd,
  GR32,
  GR32_Clipboard,
  GR32.ImageFormats;

//------------------------------------------------------------------------------
//
//      TImageFormatAdapterTClipboard
//
//------------------------------------------------------------------------------
// Implements IImageFormatAdapter for the TClipboard class.
//------------------------------------------------------------------------------
type
  TImageFormatAdapterTClipboard = class(TCustomImageFormatAdapter,
    IImageFormatAdapter)
  strict protected
    // IImageFormatAdapter
    function CanAssignFrom(Source: TPersistent): boolean; override;
    function AssignFrom(Dest: TCustomBitmap32; Source: TPersistent): boolean; override;
    function CanAssignTo(Dest: TPersistent): boolean; override;
    function AssignTo(Source: TCustomBitmap32; Dest: TPersistent): boolean; override;
  end;

//------------------------------------------------------------------------------
// IImageFormatAdapter
//------------------------------------------------------------------------------
function TImageFormatAdapterTClipboard.CanAssignFrom(Source: TPersistent): boolean;
begin
  Result := (Source is TClipboard) and (ImageFormatManager.ClipboardFormats.CanPasteFromClipboard);
end;

function TImageFormatAdapterTClipboard.AssignFrom(Dest: TCustomBitmap32; Source: TPersistent): boolean;
begin
  if (not (Source is TClipboard)) then
    Exit(False);

  Result := ImageFormatManager.ClipboardFormats.PasteFromClipboard(Dest);
end;

//------------------------------------------------------------------------------

function TImageFormatAdapterTClipboard.CanAssignTo(Dest: TPersistent): boolean;
begin
  Result := (Dest is TClipboard);
end;

function TImageFormatAdapterTClipboard.AssignTo(Source: TCustomBitmap32; Dest: TPersistent): boolean;
begin
  Result := (Dest is TClipboard) and CopyBitmap32ToClipboard(Source);
end;

//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------

initialization
  ImageFormatManager.RegisterImageFormat(TImageFormatAdapterTClipboard.Create, ImageFormatPriorityNormal);
end.

